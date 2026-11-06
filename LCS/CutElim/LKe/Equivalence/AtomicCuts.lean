import LCS.Item
import LCS.Util
import LCS.CutElim.LKe
import LCS.CutElim.CompletenessBridge
import LCS.FirstOrder.Equality.Completeness
import LCS.FirstOrder.Semantics.Subformulae
import Attach
import LCS.CutElim.LKe.Equivalence.AtomicCuts.ProofsStamp

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
-- Lemma 6.3.3: full_permutation
-- ===================================================================
-- ===================================================================
-- Theorem 6.3.1 (required def): lkeConclusion
-- ===================================================================
-- ===================================================================
-- Theorem 6.3.1 (required def): lkeProvable
-- ===================================================================
/-- Theorem 6.3.1 (required def): A sequent is LKe-provable if there
exists an LKeProofTree indexed at that sequent. -/
@[blueprint "chap6__definition_6_3_1"]
def lkeProvable {L : Language} (s : Sequent L) : Prop :=
  Nonempty (LKeProofTree s)

-- ===================================================================
-- Theorem 6.3.1 (required def): folkAllCutsAtomic
-- ===================================================================
-- retained: used by LCS.CutElim.LKe.Equivalence.AtomicTranslation
/-- Theorem 6.3.1 (required def): All cuts in an FOLKProofTree have
atomic cut formulae. -/
def folkAllCutsAtomic {L : Language} :
    {s : Sequent L} → FOLKProofTree s → Prop
  | _, .axiom_ _ _ => True
  | _, .onePremise _ t => folkAllCutsAtomic t
  | _, .twoPremise rule t1 t2 =>
    (match rule with
     | .cut A _ _ _ _ => LKeCut.isAtomic A
     | _ => True) ∧ folkAllCutsAtomic t1 ∧
    folkAllCutsAtomic t2

-- ===================================================================
-- Theorem 6.3.1 (helper): lkeStep2CutAtomic
-- ===================================================================
/-- The rule-local atomic-cut condition for a canonical LKe
two-premise node. Non-cut LK rules satisfy it vacuously. -/
@[blueprint "chap6__definition_6_3_2"]
def lkeStep2CutAtomic {L : Language}
    {prem1 prem2 conc : Sequent L} :
    FOLKStep2 prem1 prem2 conc → Prop
  | .cut A _ _ _ _ => LKeCut.isAtomic A
  | _ => True

-- ===================================================================
-- Theorem 6.3.1 (required def): lkeAllCutsAtomic
-- ===================================================================
/-- Theorem 6.3.1 (required def): Predicate asserting that every cut
in an LKe proof tree has an atomic cut formula. -/
@[blueprint "chap6__theorem_6_3_1"]
def lkeAllCutsAtomic {L : Language} :
    {s : Sequent L} → LKeProofTree s → Prop
  | _, .axiom_ _ _ => True
  | _, .eqAxiom _ _ => True
  | _, .onePremise _ t => lkeAllCutsAtomic t
  | _, .twoPremise rule t1 t2 =>
    lkeStep2CutAtomic rule ∧ lkeAllCutsAtomic t1 ∧
      lkeAllCutsAtomic t2

/-- Theorem 6.4.2 (companion, LK_e note): Every cut formula in the proof
tree is an equation `s ≐ t`. The condition checks every cut node and both
subtrees of every two-premise rule. -/
@[blueprint "chap6__theorem_6_4_2"]
def lkeAllCutsEquational {L : Language} :
    {s : Sequent L} → LKeProofTree s → Prop
  | _, .axiom_ _ _ => True
  | _, .eqAxiom _ _ => True
  | _, .onePremise _ t => lkeAllCutsEquational t
  | _, .twoPremise rule t1 t2 =>
    (match rule with
     | .cut A _ _ _ _ =>
       match A with
       | .eq_ _ _ _ => True
       | _ => False
     | _ => True) ∧ lkeAllCutsEquational t1 ∧ lkeAllCutsEquational t2

-- retained: used by LCS.CutElim.LKe.Equivalence.AtomicTranslation, LCS.CutElim.LKe.Equivalence.EqualityTranslation
/-- Compatibility of the atomic-cut predicate with the recursive
`LKeProofTree.lk` smart embedding. -/
@[simp]
theorem lkeAllCutsAtomic_lk {L : Language} {s : Sequent L}
    (t : FOLKProofTree s) :
    lkeAllCutsAtomic (LKeProofTree.lk t) ↔ folkAllCutsAtomic t := by
  induction t with
  | axiom_ _ _ => rfl
  | onePremise _ _ ih =>
      simpa [LKeProofTree.lk, lkeAllCutsAtomic,
        folkAllCutsAtomic] using ih
  | twoPremise rule _ _ ih1 ih2 =>
      cases rule <;>
        simp_all [LKeProofTree.lk, lkeAllCutsAtomic,
          folkAllCutsAtomic, lkeStep2CutAtomic]

/-- An LKe proof tree bundled with its all-cuts-atomic certificate. -/
abbrev LKeAtomicProofTree {L : Language} (s : Sequent L) :=
  {T : LKeProofTree s // lkeAllCutsAtomic T}

namespace LKeAtomicProofTree

/-- Apply a canonical one-premise LKe rule to a certified proof. -/
def onePremise {L : Language} {prem conc : Sequent L}
    (rule : FOLKStep1 prem conc) (t : LKeAtomicProofTree prem) :
    LKeAtomicProofTree conc :=
  ⟨LKeProofTree.onePremise rule t.1, t.2⟩

/-- Apply a canonical two-premise LKe rule when its root cut, if any,
is atomic. -/
def twoPremise {L : Language}
    {prem1 prem2 conc : Sequent L}
    (rule : FOLKStep2 prem1 prem2 conc)
    (hRule : lkeStep2CutAtomic rule)
    (t1 : LKeAtomicProofTree prem1)
    (t2 : LKeAtomicProofTree prem2) :
    LKeAtomicProofTree conc :=
  ⟨LKeProofTree.twoPremise rule t1.1 t2.1,
    hRule, t1.2, t2.2⟩

/-- Apply an atomic cut to two certified LKe proofs. -/
def cut {L : Language} (A : FormulaN L)
    (Γ Δ Λ Θ : List (FormulaN L))
    (hA : LKeCut.isAtomic A)
    (t1 : LKeAtomicProofTree
      (Sequent.mk Γ (Δ ++ [A])))
    (t2 : LKeAtomicProofTree
      (Sequent.mk (A :: Λ) Θ)) :
    LKeAtomicProofTree
      (Sequent.mk (Γ ++ Λ) (Δ ++ Θ)) :=
  twoPremise (.cut A Γ Δ Λ Θ) hA t1 t2

end LKeAtomicProofTree

-- ===================================================================
-- Theorem 6.3.1 (required def): lkeProof_to_geqProof
-- ===================================================================
/-- Theorem 6.3.1 (required def): Converts an LKe-proof tree to a G=-proof
tree of the same end sequent under the §6.1 sequent-level free/bound
convention (E-CUTFB). -/
@[blueprint "chap6__theorem_6_3_1" (main := true)]
noncomputable def lkeProof_to_geqProof {L : Language} (hL : L.hasEquality = true)
    {s : Sequent L} (hCross : crossNoFreeBound s) :
    LKeProofTree s → GEqProofTree hL s := by
  -- REPAIR(T6-11): proof pending
  sorry

open LCS.FirstOrder.Equality

attribute [blueprint "chap6__theorem_6_3_1"] LKeAtomicProofTree

end LCS.CutElim.LKe.Equivalence
end
