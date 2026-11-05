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

-- ATTACH-BLOCKER: unsupported untagged abbrev
/-- An LKe proof tree bundled with its all-cuts-atomic certificate. -/
abbrev LKeAtomicProofTree {L : Language} (s : Sequent L) :=
  {T : LKeProofTree s // lkeAllCutsAtomic T}

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
namespace LKeAtomicProofTree

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Apply a canonical one-premise LKe rule to a certified proof. -/
def onePremise {L : Language} {prem conc : Sequent L}
    (rule : FOLKStep1 prem conc) (t : LKeAtomicProofTree prem) :
    LKeAtomicProofTree conc :=
  ⟨LKeProofTree.onePremise rule t.1, t.2⟩

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
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

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
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

/-- Theorem 6.3.1 (required def): A sequent is LKe-provable without
essential cuts if there exists an LKeProofTree indexed at that
sequent in which every cut (if any) has an atomic cut formula. -/
@[blueprint "chap6__theorem_6_3_1"]
def lkeProvableWithoutEssentialCuts {L : Language}
    (s : Sequent L) : Prop :=
  ∃ (T : LKeProofTree s), lkeAllCutsAtomic T

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

-- ATTACH-BLOCKER: termination suffix
/-- Move a selected antecedent formula left across a finite context using
adjacent exchanges. The construction preserves both the atomic-cut and
equational-cut invariants, and requires no decidable equality on formulas. -/
def lkeMoveLeftToFront {L : Language}
    (pre mid post Δ : List (FormulaN L)) (A : FormulaN L)
    (T : LKeProofTree (Sequent.mk (pre ++ mid ++ [A] ++ post) Δ)) :
    {U : LKeProofTree (Sequent.mk (pre ++ [A] ++ mid ++ post) Δ) //
      (lkeAllCutsAtomic U ↔ lkeAllCutsAtomic T) ∧
      (lkeAllCutsEquational U ↔ lkeAllCutsEquational T)} := by
  cases mid with
  | nil => exact transport (by simp) T
  | cons B rest =>
    let q1 := transport (s' := Sequent.mk ((pre ++ [B]) ++ rest ++ [A] ++ post) Δ)
      (by simp) T
    let q2 := lkeMoveLeftToFront (pre ++ [B]) rest post Δ A q1.val
    let q3 := transport (s' := Sequent.mk (pre ++ [B, A] ++ (rest ++ post)) Δ)
      (by simp) q2.val
    let q4 := LKeProofTree.onePremise
      (.exchangeLeft pre B A (rest ++ post) Δ) q3.val
    let q5 := transport (s' := Sequent.mk (pre ++ [A] ++ (B :: rest) ++ post) Δ)
      (by simp) q4
    exact ⟨q5.val,
      q5.property.1.trans (q3.property.1.trans (q2.property.1.trans q1.property.1)),
      q5.property.2.trans (q3.property.2.trans (q2.property.2.trans q1.property.2))⟩
termination_by structural mid
where
  transport {L : Language} {s s' : Sequent L} (h : s = s') (T : LKeProofTree s) :
      {U : LKeProofTree s' //
        (lkeAllCutsAtomic U ↔ lkeAllCutsAtomic T) ∧
        (lkeAllCutsEquational U ↔ lkeAllCutsEquational T)} := by
    cases h
    exact ⟨T, Iff.rfl, Iff.rfl⟩

-- ATTACH-BLOCKER: unsupported untagged example
example {L : Language} (A B : FormulaN L) :
    (lkeMoveLeftToFront [] [B] [] [A] A
      (.onePremise (.weakenLeft B [A] [A])
        (.axiom_ _ ⟨A, rfl, rfl⟩))).val =
    LKeProofTree.onePremise (.exchangeLeft [] B A [] [A])
      (.onePremise (.weakenLeft B [A] [A])
        (.axiom_ _ ⟨A, rfl, rfl⟩)) := rfl

-- ATTACH-BLOCKER: termination suffix
/-- Move a selected succedent formula right across a finite context by
adjacent exchanges, preserving the atomic-cut and equational-cut invariants. -/
def lkeMoveRightToEnd {L : Language}
    (pre mid post Γ : List (FormulaN L)) (A : FormulaN L)
    (T : LKeProofTree (Sequent.mk Γ (pre ++ [A] ++ mid ++ post))) :
    {U : LKeProofTree (Sequent.mk Γ (pre ++ mid ++ [A] ++ post)) //
      (lkeAllCutsAtomic U ↔ lkeAllCutsAtomic T) ∧
      (lkeAllCutsEquational U ↔ lkeAllCutsEquational T)} := by
  cases mid with
  | nil => exact lkeMoveLeftToFront.transport (by simp) T
  | cons B rest =>
    let q1 := lkeMoveLeftToFront.transport
      (s' := Sequent.mk Γ (pre ++ [A, B] ++ (rest ++ post))) (by simp) T
    let q2 := LKeProofTree.onePremise
      (.exchangeRight Γ pre A B (rest ++ post)) q1.val
    let q3 := lkeMoveLeftToFront.transport
      (s' := Sequent.mk Γ ((pre ++ [B]) ++ [A] ++ rest ++ post)) (by simp) q2
    let q4 := lkeMoveRightToEnd (pre ++ [B]) rest post Γ A q3.val
    let q5 := lkeMoveLeftToFront.transport
      (s' := Sequent.mk Γ (pre ++ (B :: rest) ++ [A] ++ post)) (by simp) q4.val
    exact ⟨q5.val,
      q5.property.1.trans (q4.property.1.trans (q3.property.1.trans q1.property.1)),
      q5.property.2.trans (q4.property.2.trans (q3.property.2.trans q1.property.2))⟩
termination_by structural mid

-- ATTACH-BLOCKER: termination suffix
/-- Add an antecedent prefix and a succedent suffix using weakening rules.
The construction preserves the atomic-cut and equational-cut invariants. -/
def lkeWeakenContexts {L : Language}
    (leftExtra rightExtra Γ Δ : List (FormulaN L)) (T : LKeProofTree (Sequent.mk Γ Δ)) :
    {U : LKeProofTree (Sequent.mk (leftExtra ++ Γ) (Δ ++ rightExtra)) //
      (lkeAllCutsAtomic U ↔ lkeAllCutsAtomic T) ∧
      (lkeAllCutsEquational U ↔ lkeAllCutsEquational T)} := by
  cases leftExtra with
  | nil => exact weakenRight rightExtra Γ Δ T
  | cons A rest =>
    let q := lkeWeakenContexts rest rightExtra Γ Δ T
    exact ⟨.onePremise (.weakenLeft A (rest ++ Γ) (Δ ++ rightExtra)) q.val, q.property⟩
termination_by structural leftExtra
where
  weakenRight {L : Language} (rightExtra Γ Δ : List (FormulaN L))
      (T : LKeProofTree (Sequent.mk Γ Δ)) :
      {U : LKeProofTree (Sequent.mk Γ (Δ ++ rightExtra)) //
        (lkeAllCutsAtomic U ↔ lkeAllCutsAtomic T) ∧
        (lkeAllCutsEquational U ↔ lkeAllCutsEquational T)} := by
    cases rightExtra with
    | nil => exact lkeMoveLeftToFront.transport (by simp) T
    | cons A rest =>
      let q1 := LKeProofTree.onePremise (.weakenRight A Γ Δ) T
      let q2 := weakenRight rest Γ (Δ ++ [A]) q1
      let q3 := lkeMoveLeftToFront.transport
        (s' := Sequent.mk Γ (Δ ++ (A :: rest))) (by simp) q2.val
      exact ⟨q3.val, q3.property.1.trans q2.property.1,
        q3.property.2.trans q2.property.2⟩
  termination_by structural rightExtra

-- ATTACH-BLOCKER: unsupported untagged example
example {L : Language} (A B : FormulaN L) :
    (lkeMoveRightToEnd [] [B] [] [A] A
      (.onePremise (.weakenRight B [A] [A])
        (.axiom_ _ ⟨A, rfl, rfl⟩))).val =
    LKeProofTree.onePremise (.exchangeRight [A] [] A B [])
      (.onePremise (.weakenRight B [A] [A])
        (.axiom_ _ ⟨A, rfl, rfl⟩)) := rfl

-- ATTACH-BLOCKER: unsupported untagged example
example {L : Language} (A B C : FormulaN L) :
    (lkeWeakenContexts [B] [C] [A] [A]
      (.axiom_ _ ⟨A, rfl, rfl⟩)).val =
    LKeProofTree.onePremise (.weakenLeft B [A] [A, C])
      (.onePremise (.weakenRight C [A] [A])
        (.axiom_ _ ⟨A, rfl, rfl⟩)) := rfl

-- retained: used by LCS.CutElim.LKe.Equivalence.AtomicTranslation
/-- Contract duplicate antecedent and succedent contexts by exchanges and
contractions. Both cut invariants are preserved. -/
def lkeContractContexts {L : Language} (Γ Δ : List (FormulaN L))
    (T : LKeProofTree (Sequent.mk (Γ ++ Γ) (Δ ++ Δ))) :
    {U : LKeProofTree (Sequent.mk Γ Δ) //
      (lkeAllCutsAtomic U ↔ lkeAllCutsAtomic T) ∧
      (lkeAllCutsEquational U ↔ lkeAllCutsEquational T)} := by
  let a := lkeMoveLeftToFront.transport
    (s' := Sequent.mk ([] ++ Γ ++ Γ) (Δ ++ Δ)) (by simp) T
  let b := left [] Γ (Δ ++ Δ) a.val
  let c := lkeMoveLeftToFront.transport
    (s' := Sequent.mk Γ ([] ++ Δ ++ Δ)) (by simp) b.val
  let d := right [] Δ Γ c.val
  let e := lkeMoveLeftToFront.transport (s' := Sequent.mk Γ Δ) (by simp) d.val
  exact ⟨e.val, e.property.1.trans (d.property.1.trans (c.property.1.trans
    (b.property.1.trans a.property.1))), e.property.2.trans (d.property.2.trans
    (c.property.2.trans (b.property.2.trans a.property.2)))⟩
where
  leftBack {L : Language} (pre mid post Δ : List (FormulaN L))
      (A : FormulaN L)
      (T : LKeProofTree (Sequent.mk (pre ++ [A] ++ mid ++ post) Δ)) :
      {U : LKeProofTree (Sequent.mk (pre ++ mid ++ [A] ++ post) Δ) //
        (lkeAllCutsAtomic U ↔ lkeAllCutsAtomic T) ∧
        (lkeAllCutsEquational U ↔ lkeAllCutsEquational T)} := by
    cases mid with
    | nil => exact lkeMoveLeftToFront.transport (by simp) T
    | cons B rest =>
      let a := lkeMoveLeftToFront.transport
        (s' := Sequent.mk (pre ++ [A, B] ++ (rest ++ post)) Δ) (by simp) T
      let b := LKeProofTree.onePremise (.exchangeLeft pre A B (rest ++ post) Δ) a.val
      let c := lkeMoveLeftToFront.transport
        (s' := Sequent.mk ((pre ++ [B]) ++ [A] ++ rest ++ post) Δ) (by simp) b
      let d := leftBack (pre ++ [B]) rest post Δ A c.val
      let e := lkeMoveLeftToFront.transport
        (s' := Sequent.mk (pre ++ (B :: rest) ++ [A] ++ post) Δ) (by simp) d.val
      exact ⟨e.val, e.property.1.trans (d.property.1.trans (c.property.1.trans (a.property.1))), e.property.2.trans (d.property.2.trans (c.property.2.trans (a.property.2)))⟩
  termination_by structural mid

  rightFront {L : Language} (pre mid post Δ : List (FormulaN L))
      (A : FormulaN L)
      (T : LKeProofTree (Sequent.mk Δ (pre ++ mid ++ [A] ++ post))) :
      {U : LKeProofTree (Sequent.mk Δ (pre ++ [A] ++ mid ++ post)) //
        (lkeAllCutsAtomic U ↔ lkeAllCutsAtomic T) ∧
        (lkeAllCutsEquational U ↔ lkeAllCutsEquational T)} := by
    cases mid with
    | nil => exact lkeMoveLeftToFront.transport (by simp) T
    | cons B rest =>
      let a := lkeMoveLeftToFront.transport
        (s' := Sequent.mk Δ ((pre ++ [B]) ++ rest ++ [A] ++ post)) (by simp) T
      let b := rightFront (pre ++ [B]) rest post Δ A a.val
      let c := lkeMoveLeftToFront.transport
        (s' := Sequent.mk Δ (pre ++ [B, A] ++ (rest ++ post))) (by simp) b.val
      let d := LKeProofTree.onePremise (.exchangeRight Δ pre B A (rest ++ post)) c.val
      let e := lkeMoveLeftToFront.transport
        (s' := Sequent.mk Δ (pre ++ [A] ++ (B :: rest) ++ post)) (by simp) d
      exact ⟨e.val, e.property.1.trans (c.property.1.trans (b.property.1.trans (a.property.1))), e.property.2.trans (c.property.2.trans (b.property.2.trans (a.property.2)))⟩
  termination_by structural mid

  left {L : Language} (pfx lst Δ : List (FormulaN L))
      (T : LKeProofTree (Sequent.mk (pfx ++ lst ++ lst) Δ)) :
      {U : LKeProofTree (Sequent.mk (pfx ++ lst) Δ) //
        (lkeAllCutsAtomic U ↔ lkeAllCutsAtomic T) ∧
        (lkeAllCutsEquational U ↔ lkeAllCutsEquational T)} := by
    cases lst with
    | nil => exact lkeMoveLeftToFront.transport (by simp) T
    | cons A rest =>
      let a := lkeMoveLeftToFront.transport
        (s' := Sequent.mk ((pfx ++ [A]) ++ rest ++ [A] ++ rest) Δ) (by simp) T
      let b := lkeMoveLeftToFront (pfx ++ [A]) rest rest Δ A a.val
      let c := lkeMoveLeftToFront.transport
        (s' := Sequent.mk ([] ++ (pfx ++ [A]) ++ [A] ++ (rest ++ rest)) Δ) (by simp) b.val
      let d := lkeMoveLeftToFront [] (pfx ++ [A]) (rest ++ rest) Δ A c.val
      let e := lkeMoveLeftToFront.transport
        (s' := Sequent.mk ([A] ++ pfx ++ [A] ++ (rest ++ rest)) Δ) (by simp) d.val
      let f := lkeMoveLeftToFront [A] pfx (rest ++ rest) Δ A e.val
      let g := lkeMoveLeftToFront.transport
        (s' := Sequent.mk (A :: A :: (pfx ++ rest ++ rest)) Δ) (by simp) f.val
      let h := LKeProofTree.onePremise (.contractLeft A (pfx ++ rest ++ rest) Δ) g.val
      let j := lkeMoveLeftToFront.transport
        (s' := Sequent.mk ([] ++ [A] ++ pfx ++ (rest ++ rest)) Δ) (by simp) h
      let k := leftBack [] pfx (rest ++ rest) Δ A j.val
      let m := lkeMoveLeftToFront.transport
        (s' := Sequent.mk ((pfx ++ [A]) ++ rest ++ rest) Δ) (by simp) k.val
      let n := left (pfx ++ [A]) rest Δ m.val
      let out := lkeMoveLeftToFront.transport
        (s' := Sequent.mk (pfx ++ (A :: rest)) Δ) (by simp) n.val
      exact ⟨out.val, out.property.1.trans (n.property.1.trans (m.property.1.trans (k.property.1.trans (j.property.1.trans (g.property.1.trans (f.property.1.trans (e.property.1.trans (d.property.1.trans (c.property.1.trans (b.property.1.trans (a.property.1))))))))))), out.property.2.trans (n.property.2.trans (m.property.2.trans (k.property.2.trans (j.property.2.trans (g.property.2.trans (f.property.2.trans (e.property.2.trans (d.property.2.trans (c.property.2.trans (b.property.2.trans (a.property.2)))))))))))⟩
  termination_by structural lst

  right {L : Language} (pfx lst Γ : List (FormulaN L))
      (T : LKeProofTree (Sequent.mk Γ (pfx ++ lst ++ lst))) :
      {U : LKeProofTree (Sequent.mk Γ (pfx ++ lst)) //
        (lkeAllCutsAtomic U ↔ lkeAllCutsAtomic T) ∧
        (lkeAllCutsEquational U ↔ lkeAllCutsEquational T)} := by
    cases lst with
    | nil => exact lkeMoveLeftToFront.transport (by simp) T
    | cons A rest =>
      let a := lkeMoveLeftToFront.transport
        (s' := Sequent.mk Γ ((pfx ++ [A]) ++ rest ++ [A] ++ rest)) (by simp) T
      let b := rightFront (pfx ++ [A]) rest rest Γ A a.val
      let c := lkeMoveLeftToFront.transport
        (s' := Sequent.mk Γ ((pfx ++ [A]) ++ [A] ++ (rest ++ rest) ++ [])) (by simp) b.val
      let d := lkeMoveRightToEnd (pfx ++ [A]) (rest ++ rest) [] Γ A c.val
      let e := lkeMoveLeftToFront.transport
        (s' := Sequent.mk Γ (pfx ++ [A] ++ (rest ++ rest ++ [A]) ++ [])) (by simp) d.val
      let f := lkeMoveRightToEnd pfx (rest ++ rest ++ [A]) [] Γ A e.val
      let g := lkeMoveLeftToFront.transport
        (s' := Sequent.mk Γ ((pfx ++ rest ++ rest) ++ [A, A])) (by simp) f.val
      let h := LKeProofTree.onePremise (.contractRight A Γ (pfx ++ rest ++ rest)) g.val
      let j := lkeMoveLeftToFront.transport
        (s' := Sequent.mk Γ (pfx ++ (rest ++ rest) ++ [A] ++ [])) (by simp) h
      let k := rightFront pfx (rest ++ rest) [] Γ A j.val
      let m := lkeMoveLeftToFront.transport
        (s' := Sequent.mk Γ ((pfx ++ [A]) ++ rest ++ rest)) (by simp) k.val
      let n := right (pfx ++ [A]) rest Γ m.val
      let out := lkeMoveLeftToFront.transport
        (s' := Sequent.mk Γ (pfx ++ (A :: rest))) (by simp) n.val
      exact ⟨out.val, out.property.1.trans (n.property.1.trans (m.property.1.trans (k.property.1.trans (j.property.1.trans (g.property.1.trans (f.property.1.trans (e.property.1.trans (d.property.1.trans (c.property.1.trans (b.property.1.trans (a.property.1))))))))))), out.property.2.trans (n.property.2.trans (m.property.2.trans (k.property.2.trans (j.property.2.trans (g.property.2.trans (f.property.2.trans (e.property.2.trans (d.property.2.trans (c.property.2.trans (b.property.2.trans (a.property.2)))))))))))⟩
  termination_by structural lst

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
namespace ConjProjection

-- ATTACH-BLOCKER: unsupported untagged inductive
/-- Select succedent occurrences of a conjunction and record their chosen conjunct. -/
inductive Mask {L : Language} (A B : FormulaN L) (pick : Bool) :
    List (FormulaN L) → List (FormulaN L) → Type where
  | nil : Mask A B pick [] []
  | keep (F : FormulaN L) {xs ys} (tail : Mask A B pick xs ys) :
      Mask A B pick (F :: xs) (F :: ys)
  | project {xs ys} (tail : Mask A B pick xs ys) :
      Mask A B pick (FormulaN.conj A B :: xs) ((if pick then A else B) :: ys)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Leave every formula occurrence unchanged. -/
def Mask.refl {L : Language} {A B : FormulaN L} {pick} :
    (xs : List (FormulaN L)) → Mask A B pick xs xs
  | [] => .nil
  | F :: xs => .keep F (Mask.refl xs)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Concatenate two occurrence selections. -/
def Mask.append {L : Language} {A B : FormulaN L} {pick xs xs' ys ys'}
    (p : Mask A B pick xs xs') (q : Mask A B pick ys ys') :
    Mask A B pick (xs ++ ys) (xs' ++ ys') :=
  match p with
  | .nil => q
  | .keep F p => .keep F (p.append q)
  | .project p => .project (p.append q)

-- ATTACH-BLOCKER: termination suffix
/-- Split an occurrence selection at a given source-context boundary. -/
def Mask.split {L : Language} {A B : FormulaN L} {pick}
    (xs ys : List (FormulaN L)) {zs} (p : Mask A B pick (xs ++ ys) zs) :
    Σ xs' ys', {_q : Mask A B pick xs xs' × Mask A B pick ys ys' // zs = xs' ++ ys'} := by
  cases xs with
  | nil => exact ⟨[], zs, ⟨.nil, p⟩, rfl⟩
  | cons F rest =>
    cases p with
    | keep F p =>
      obtain ⟨xs', ys', ⟨p, q⟩, h⟩ := Mask.split rest ys p
      exact ⟨F :: xs', ys', ⟨.keep F p, q⟩, by simp [h]⟩
    | project p =>
      obtain ⟨xs', ys', ⟨p, q⟩, h⟩ := Mask.split rest ys p
      exact ⟨(if pick then A else B) :: xs', ys', ⟨.project p, q⟩, by simp [h]⟩
termination_by structural xs

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Read the resulting formula of a singleton occurrence selection. -/
def Mask.singleton {L : Language} {A B : FormulaN L} {pick F ys}
    (p : Mask A B pick [F] ys) : {G : FormulaN L // ys = [G]} := by
  cases p with
  | keep F p => cases p; exact ⟨F, rfl⟩
  | project p => cases p; exact ⟨if pick then A else B, rfl⟩

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Selecting a conjunct preserves eigenvariable freshness. -/
theorem Mask.fresh {L : Language} {A B : FormulaN L} {pick xs ys}
    (p : Mask A B pick xs ys) (x : Nat)
    (h : ∀ F ∈ xs, x ∉ formulaFVN F) : ∀ F ∈ ys, x ∉ formulaFVN F := by
  induction p with
  | nil => simp
  | keep F p ih =>
    intro G hG
    rcases List.mem_cons.mp hG with rfl | hG
    · exact h _ List.mem_cons_self
    · exact ih (fun H hH => h H (List.mem_cons_of_mem _ hH)) G hG
  | project p ih =>
    intro G hG
    rcases List.mem_cons.mp hG with rfl | hG
    · have hAB := h (FormulaN.conj A B) List.mem_cons_self
      cases pick with
      | false => exact fun hx => hAB (Or.inr hx)
      | true => exact fun hx => hAB (Or.inl hx)
    · exact ih (fun H hH => h H (List.mem_cons_of_mem _ hH)) G hG

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Rebuild a unary rule using a recursive projection callback. -/
def one {L : Language} (A B : FormulaN L) (pick : Bool)
    {prem conc : Sequent L} (rule : FOLKStep1 prem conc)
    (ih : ∀ {out}, Mask A B pick prem.succedent out → LKeProofTree (Sequent.mk prem.antecedent out))
    {out} (m : Mask A B pick conc.succedent out) :
    LKeProofTree (Sequent.mk conc.antecedent out) := by
  cases rule with
  | weakenLeft F Γ Δ =>
    exact .onePremise (.weakenLeft F Γ out) (ih m)
  | contractLeft F Γ Δ =>
    exact .onePremise (.contractLeft F Γ out) (ih m)
  | exchangeLeft Γ F G Δ Λ =>
    exact .onePremise (.exchangeLeft Γ F G Δ out) (ih m)
  | andLeftL F G Γ Δ =>
    exact .onePremise (.andLeftL F G Γ out) (ih m)
  | andLeftR F G Γ Δ =>
    exact .onePremise (.andLeftR F G Γ out) (ih m)
  | allLeft t x F Γ Δ hf =>
    exact .onePremise (.allLeft t x F Γ out hf) (ih m)
  | negLeft F Γ Δ =>
    exact .onePremise (.negLeft F Γ out)
      (ih (m.append (.keep F .nil)))
  | exLeft y x F Γ Δ fresh hf =>
    refine .onePremise (.exLeft y x F Γ out ?_ hf) (ih m)
    intro G hG
    rcases List.mem_append.mp hG with hG | hG
    · exact fresh G (List.mem_append_left _ hG)
    · exact m.fresh y (fun H hH => fresh H (List.mem_append_right _ hH)) G hG
  | weakenRight F Γ Δ =>
    obtain ⟨Δ', last, ⟨md, ml⟩, rfl⟩ := m.split Δ [F]
    cases ml with
    | keep F tail => cases tail; exact .onePremise (.weakenRight F Γ Δ') (ih md)
    | project tail => cases tail; exact .onePremise (.weakenRight (if pick then A else B) Γ Δ') (ih md)
  | contractRight F Γ Δ =>
    obtain ⟨Δ', last, ⟨md, ml⟩, rfl⟩ := m.split Δ [F]
    cases ml with
    | keep F tail =>
      cases tail
      exact .onePremise (.contractRight F Γ Δ')
        (ih (md.append (.keep F (.keep F .nil))))
    | project tail =>
      cases tail
      exact .onePremise (.contractRight (if pick then A else B) Γ Δ')
        (ih (md.append (.project (.project .nil))))
  | orRightL F G Γ Δ =>
    obtain ⟨Δ', last, ⟨md, ml⟩, rfl⟩ := m.split Δ [FormulaN.disj F G]
    cases ml with
    | keep _ tail =>
      cases tail
      exact .onePremise (.orRightL F G Γ Δ')
        (ih (md.append (.keep (F) .nil)))
  | orRightR F G Γ Δ =>
    obtain ⟨Δ', last, ⟨md, ml⟩, rfl⟩ := m.split Δ [FormulaN.disj F G]
    cases ml with
    | keep _ tail =>
      cases tail
      exact .onePremise (.orRightR F G Γ Δ')
        (ih (md.append (.keep (G) .nil)))
  | implRight F G Γ Δ =>
    obtain ⟨Δ', last, ⟨md, ml⟩, rfl⟩ := m.split Δ [FormulaN.impl F G]
    cases ml with
    | keep _ tail =>
      cases tail
      exact .onePremise (.implRight F G Γ Δ')
        (ih (md.append (.keep (G) .nil)))
  | negRight F Γ Δ =>
    obtain ⟨Δ', last, ⟨md, ml⟩, rfl⟩ := m.split Δ [FormulaN.neg F]
    cases ml with
    | keep _ tail =>
      cases tail
      exact .onePremise (.negRight F Γ Δ') (ih md)
  | exRight t x F Γ Δ hf =>
    obtain ⟨Δ', last, ⟨md, ml⟩, rfl⟩ := m.split Δ [FormulaN.ex x F]
    cases ml with
    | keep _ tail =>
      cases tail
      exact .onePremise (.exRight t x F Γ Δ' hf)
        (ih (md.append (.keep (formulaSubstN F t x) .nil)))
  | allRight y x F Γ Δ fresh hf =>
    obtain ⟨Δ', last, ⟨md, ml⟩, rfl⟩ := m.split Δ [FormulaN.all x F]
    cases ml with
    | keep _ tail =>
      cases tail
      refine .onePremise (.allRight y x F Γ Δ' ?_ hf)
        (ih (md.append (.keep (formulaSubstN F (Term.var y) x) .nil)))
      intro G hG
      rcases List.mem_append.mp hG with hG | hG
      · exact fresh G (List.mem_append_left _ hG)
      · exact (md.append (.keep (FormulaN.all x F) .nil)).fresh y
          (fun H hH => fresh H (List.mem_append_right _ hH)) G hG
  | exchangeRight Γ Δ F G Λ =>
    obtain ⟨Δ', tail, ⟨md, mt⟩, hout⟩ := Mask.split Δ ([G, F] ++ Λ) (by simpa [List.append_assoc] using m)
    obtain ⟨mid, Λ', ⟨mm, ml⟩, htail⟩ := mt.split [G, F] Λ
    obtain ⟨gs, fs, ⟨mg, mf⟩, hmid⟩ := mm.split [G] [F]
    obtain ⟨G', hg⟩ := mg.singleton
    obtain ⟨F', hf⟩ := mf.singleton
    subst gs; subst fs; subst mid; subst tail; subst out
    have mask : Mask A B pick (Δ ++ [F, G] ++ Λ) (Δ' ++ [F', G'] ++ Λ') := by
      simpa [List.append_assoc] using md.append ((mf.append mg).append ml)
    simpa [List.append_assoc] using LKeProofTree.onePremise
      (.exchangeRight Γ Δ' F' G' Λ') (ih mask)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Rebuild a binary rule using recursive projection callbacks. -/
def two {L : Language} (A B : FormulaN L) (pick : Bool)
    {prem1 prem2 conc : Sequent L} (rule : FOLKStep2 prem1 prem2 conc)
    (ih1 : ∀ {out}, Mask A B pick prem1.succedent out → LKeProofTree (Sequent.mk prem1.antecedent out))
    (ih2 : ∀ {out}, Mask A B pick prem2.succedent out → LKeProofTree (Sequent.mk prem2.antecedent out))
    {out} (m : Mask A B pick conc.succedent out) :
    LKeProofTree (Sequent.mk conc.antecedent out) := by
  cases rule with
  | cut F Γ Δ Λ Θ =>
    obtain ⟨Δ', Θ', ⟨md, mt⟩, rfl⟩ := m.split Δ Θ
    exact .twoPremise (.cut F Γ Δ' Λ Θ')
      (ih1 (md.append (.keep F .nil)))
      (ih2 mt)
  | orLeft F G Γ Δ =>
    exact .twoPremise (.orLeft F G Γ out)
      (ih1 m) (ih2 m)
  | implLeft F G Γ Δ Λ Θ =>
    obtain ⟨Δ', Θ', ⟨md, mt⟩, rfl⟩ := m.split Δ Θ
    exact .twoPremise (.implLeft F G Γ Δ' Λ Θ')
      (ih1 (md.append (.keep F .nil)))
      (ih2 mt)
  | andRight F G Γ Δ =>
    obtain ⟨Δ', last, ⟨md, ml⟩, rfl⟩ := m.split Δ [FormulaN.conj F G]
    cases ml with
    | keep _ tail =>
      cases tail
      exact .twoPremise (.andRight F G Γ Δ')
        (ih1 (md.append (.keep F .nil)))
        (ih2 (md.append (.keep G .nil)))
    | project tail =>
      cases tail
      cases pick with
      | false => exact ih2 (md.append (.keep B .nil))
      | true => exact ih1 (md.append (.keep A .nil))

-- ATTACH-BLOCKER: termination suffix
/-- Project selected conjunction occurrences by structural recursion on the tree. -/
def invert {L : Language} (A B : FormulaN L) (pick : Bool)
    {s : Sequent L} (T : LKeProofTree s) {out : List (FormulaN L)}
    (m : Mask A B pick s.succedent out) : LKeProofTree (Sequent.mk s.antecedent out) :=
  match T with
  | .axiom_ s hAx => by
    cases s with
    | mk Γ Δ =>
      cases m with
      | nil => exact False.elim (by obtain ⟨F, _, h⟩ := hAx; cases h)
      | keep F m =>
        rename_i xs ys
        have h : Γ = [F] ∧ xs = [] := by
          obtain ⟨G, hΓ, hΔ⟩ := hAx
          simp only [Sequent.antecedent, Sequent.succedent, List.cons.injEq] at hΓ hΔ
          exact ⟨hΓ.trans (congrArg (fun x => [x]) hΔ.1.symm), hΔ.2⟩
        rcases h with ⟨rfl, h⟩
        cases h
        cases m
        exact .axiom_ _ ⟨F, rfl, rfl⟩
      | project m =>
        rename_i xs ys
        have h : Γ = [FormulaN.conj A B] ∧ xs = [] := by
          obtain ⟨G, hΓ, hΔ⟩ := hAx
          simp only [Sequent.antecedent, Sequent.succedent, List.cons.injEq] at hΓ hΔ
          exact ⟨hΓ.trans (congrArg (fun x => [x]) hΔ.1.symm), hΔ.2⟩
        rcases h with ⟨rfl, h⟩
        cases h
        cases m
        cases pick with
        | false => exact .onePremise (.andLeftR A B [] [B]) (.axiom_ _ ⟨B, rfl, rfl⟩)
        | true => exact .onePremise (.andLeftL A B [] [A]) (.axiom_ _ ⟨A, rfl, rfl⟩)
  | .eqAxiom hL ax => by
    cases ax with
    | refl t => cases m; rename_i tail; cases tail; exact .eqAxiom hL (.refl t)
    | funcCong f ss ts => cases m; rename_i tail; cases tail; exact .eqAxiom hL (.funcCong f ss ts)
    | predCong P ss ts => cases m; rename_i tail; cases tail; exact .eqAxiom hL (.predCong P ss ts)
    | eqCong s1 s2 t1 t2 => cases m; rename_i tail; cases tail; exact .eqAxiom hL (.eqCong s1 s2 t1 t2)
  | .onePremise rule sub =>
    one A B pick rule (fun {_} m => invert A B pick sub m) m
  | .twoPremise rule sub1 sub2 =>
    two A B pick rule (fun {_} m => invert A B pick sub1 m)
      (fun {_} m => invert A B pick sub2 m) m
termination_by structural T

end ConjProjection
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
open LCS.FirstOrder.Equality

-- ATTACH-BLOCKER: termination suffix
/-- Project one indexed conjunct from a finite right-associated conjunction
in the succedent by structural inversion of the proof tree. -/
def lkeProjectConjoinRight {L : Language} (d : FormulaN L)
    (atoms Γ Δ : List (FormulaN L))
    (T : LKeProofTree (Sequent.mk Γ (Δ ++ [conjoinFormulae d atoms])))
    (i : Fin atoms.length) : LKeProofTree (Sequent.mk Γ (Δ ++ [atoms[i]])) := by
  cases atoms with
  | nil => exact Fin.elim0 i
  | cons F rest =>
    cases rest with
    | nil =>
      have hi : i = 0 := by
        apply Fin.ext
        change i.val = 0
        have hn := i.isLt
        simp only [List.length_cons, List.length_nil] at hn
        omega
      subst i
      exact T
    | cons G rest =>
      cases i with
      | mk n hn =>
        cases n with
        | zero =>
          exact ConjProjection.invert F (conjoinFormulae d (G :: rest)) true T
            ((ConjProjection.Mask.refl Δ).append (.project .nil))
        | succ n =>
          let U := ConjProjection.invert F (conjoinFormulae d (G :: rest)) false T
            ((ConjProjection.Mask.refl Δ).append (.project .nil))
          exact lkeProjectConjoinRight d (G :: rest) Γ Δ U ⟨n, by simpa using hn⟩
termination_by structural atoms

-- ATTACH-BLOCKER: unsupported untagged example
example {L : Language} (A B : FormulaN L) :
    lkeProjectConjoinRight A [A, B] [FormulaN.conj A B] []
      (.axiom_ _ ⟨FormulaN.conj A B, rfl, rfl⟩) 1 =
    LKeProofTree.onePremise (.andLeftR A B [] [B])
      (.axiom_ _ ⟨B, rfl, rfl⟩) := rfl

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
open LCS.FirstOrder.Equality
namespace ImplLeftProjection

-- ATTACH-BLOCKER: unsupported untagged inductive
/-- Select antecedent implications and replace them by their consequents. -/
inductive Mask {L : Language} (A B : FormulaN L) :
    List (FormulaN L) → List (FormulaN L) → Type where
  | nil : Mask A B [] []
  | keep (F : FormulaN L) {xs ys} (tail : Mask A B xs ys) :
      Mask A B (F :: xs) (F :: ys)
  | project {xs ys} (tail : Mask A B xs ys) :
      Mask A B (FormulaN.impl A B :: xs) (B :: ys)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Leave every antecedent occurrence unchanged. -/
def Mask.refl {L : Language} {A B : FormulaN L}  :
    (xs : List (FormulaN L)) → Mask A B xs xs
  | [] => .nil
  | F :: xs => .keep F (Mask.refl xs)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Concatenate two antecedent occurrence selections. -/
def Mask.append {L : Language} {A B : FormulaN L} {xs xs' ys ys'}
    (p : Mask A B xs xs') (q : Mask A B ys ys') :
    Mask A B (xs ++ ys) (xs' ++ ys') :=
  match p with
  | .nil => q
  | .keep F p => .keep F (p.append q)
  | .project p => .project (p.append q)

-- ATTACH-BLOCKER: termination suffix
/-- Split an occurrence selection at a source-context boundary. -/
def Mask.split {L : Language} {A B : FormulaN L}
    (xs ys : List (FormulaN L)) {zs} (p : Mask A B (xs ++ ys) zs) :
    Σ xs' ys', {_q : Mask A B xs xs' × Mask A B ys ys' // zs = xs' ++ ys'} := by
  cases xs with
  | nil => exact ⟨[], zs, ⟨.nil, p⟩, rfl⟩
  | cons F rest =>
    cases p with
    | keep F p =>
      obtain ⟨xs', ys', ⟨p, q⟩, h⟩ := Mask.split rest ys p
      exact ⟨F :: xs', ys', ⟨.keep F p, q⟩, by simp [h]⟩
    | project p =>
      obtain ⟨xs', ys', ⟨p, q⟩, h⟩ := Mask.split rest ys p
      exact ⟨B :: xs', ys', ⟨.project p, q⟩, by simp [h]⟩
termination_by structural xs

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Read the resulting formula of a singleton selection. -/
def Mask.singleton {L : Language} {A B : FormulaN L} {F ys}
    (p : Mask A B [F] ys) : {G : FormulaN L // ys = [G]} := by
  cases p with
  | keep F p => cases p; exact ⟨F, rfl⟩
  | project p => cases p; exact ⟨B, rfl⟩

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Replacing selected implications by consequents preserves freshness. -/
theorem Mask.fresh {L : Language} {A B : FormulaN L} {xs ys}
    (p : Mask A B xs ys) (x : Nat)
    (h : ∀ F ∈ xs, x ∉ formulaFVN F) : ∀ F ∈ ys, x ∉ formulaFVN F := by
  induction p with
  | nil => simp
  | keep F p ih =>
    intro G hG
    rcases List.mem_cons.mp hG with rfl | hG
    · exact h _ List.mem_cons_self
    · exact ih (fun H hH => h H (List.mem_cons_of_mem _ hH)) G hG
  | project p ih =>
    intro G hG
    rcases List.mem_cons.mp hG with rfl | hG
    · have hAB := h _ List.mem_cons_self
      exact fun hx => hAB (Or.inr hx)
    · exact ih (fun H hH => h H (List.mem_cons_of_mem _ hH)) G hG


-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- An atomic antecedent has no implication occurrence to replace. -/
theorem Mask.atomicEq {L : Language} {A B : FormulaN L} {xs ys}
    (m : Mask A B xs ys) (h : ∀ F ∈ xs, F.isAtomic) : ys = xs := by
  induction m with
  | nil => rfl
  | keep F m ih =>
    exact congrArg (List.cons F) (ih (fun G hG => h G (List.mem_cons_of_mem _ hG)))
  | project m ih =>
    have hi := h _ List.mem_cons_self
    simp [FormulaN.isAtomic] at hi

-- ATTACH-BLOCKER: termination suffix
/-- Move a succedent block past its following context by adjacent exchanges. -/
def blockRight {L : Language} (pre block mid post Γ : List (FormulaN L))
    (T : LKeProofTree (Sequent.mk Γ (pre ++ block ++ mid ++ post))) :
    LKeProofTree (Sequent.mk Γ (pre ++ mid ++ block ++ post)) := by
  cases block with
  | nil => simpa using T
  | cons F rest =>
    have q1 : LKeProofTree (Sequent.mk Γ ((pre ++ [F]) ++ rest ++ mid ++ post)) := by
      simpa using T
    let q2 := blockRight (pre ++ [F]) rest mid post Γ q1
    have q3 : LKeProofTree (Sequent.mk Γ (pre ++ [F] ++ mid ++ (rest ++ post))) := by
      simpa using q2
    let q4 := lkeMoveRightToEnd pre mid (rest ++ post) Γ F q3
    simpa using q4.val
termination_by structural block

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Rebuild a unary rule using a recursive consequent-projection callback. -/
def one {L : Language} (A B : FormulaN L)
    {prem conc : Sequent L} (rule : FOLKStep1 prem conc)
    (ih : ∀ {out}, Mask A B prem.antecedent out → LKeProofTree (Sequent.mk out prem.succedent))
    {out} (m : Mask A B conc.antecedent out) :
    LKeProofTree (Sequent.mk out conc.succedent) := by
  cases rule with
  | weakenRight F Γ Δ => exact .onePremise (.weakenRight F out Δ) (ih m)
  | contractRight F Γ Δ => exact .onePremise (.contractRight F out Δ) (ih m)
  | exchangeRight Γ Δ F G Λ => exact .onePremise (.exchangeRight out Δ F G Λ) (ih m)
  | orRightL F G Γ Δ => exact .onePremise (.orRightL F G out Δ) (ih m)
  | orRightR F G Γ Δ => exact .onePremise (.orRightR F G out Δ) (ih m)
  | exRight t x F Γ Δ hf => exact .onePremise (.exRight t x F out Δ hf) (ih m)
  | negRight F Γ Δ => exact .onePremise (.negRight F out Δ) (ih (.keep F m))
  | implRight F G Γ Δ => exact .onePremise (.implRight F G out Δ) (ih (.keep F m))
  | allRight y x F Γ Δ fresh hf =>
    refine .onePremise (.allRight y x F out Δ ?_ hf) (ih m)
    intro G hG
    rcases List.mem_append.mp hG with hG | hG
    · exact m.fresh y (fun H hH => fresh H (List.mem_append_left _ hH)) G hG
    · exact fresh G (List.mem_append_right _ hG)
  | weakenLeft F Γ Δ =>
    cases m with
    | keep F m => exact .onePremise (.weakenLeft F _ Δ) (ih m)
    | project m => exact .onePremise (.weakenLeft B _ Δ) (ih m)
  | contractLeft F Γ Δ =>
    cases m with
    | keep F m => exact .onePremise (.contractLeft F _ Δ) (ih (.keep F (.keep F m)))
    | project m => exact .onePremise (.contractLeft B _ Δ) (ih (.project (.project m)))
  | andLeftL F G Γ Δ =>
    cases m with
    | keep _ m => exact .onePremise (.andLeftL F G _ Δ) (ih (.keep F m))
  | andLeftR F G Γ Δ =>
    cases m with
    | keep _ m => exact .onePremise (.andLeftR F G _ Δ) (ih (.keep G m))
  | negLeft F Γ Δ =>
    cases m with
    | keep _ m => exact .onePremise (.negLeft F _ Δ) (ih m)
  | allLeft t x F Γ Δ hf =>
    cases m with
    | keep _ m =>
      exact .onePremise (.allLeft t x F _ Δ hf) (ih (.keep (formulaSubstN F t x) m))
  | exLeft y x F Γ Δ fresh hf =>
    cases m with
    | keep _ m =>
      refine .onePremise (.exLeft y x F _ Δ ?_ hf)
        (ih (.keep (formulaSubstN F (Term.var y) x) m))
      intro G hG
      rcases List.mem_append.mp hG with hG | hG
      · exact (Mask.keep (FormulaN.ex x F) m).fresh y
          (fun H hH => fresh H (List.mem_append_left _ hH)) G hG
      · exact fresh G (List.mem_append_right _ hG)
  | exchangeLeft Γ F G Δ Λ =>
    obtain ⟨Γ', tail, ⟨mg, mt⟩, hout⟩ := Mask.split Γ ([G, F] ++ Δ)
      (by simpa [List.append_assoc] using m)
    obtain ⟨mid, Δ', ⟨mm, md⟩, htail⟩ := mt.split [G, F] Δ
    obtain ⟨gs, fs, ⟨mG, mF⟩, hmid⟩ := mm.split [G] [F]
    obtain ⟨G', hg⟩ := mG.singleton
    obtain ⟨F', hf⟩ := mF.singleton
    subst gs; subst fs; subst mid; subst tail; subst out
    have mask : Mask A B (Γ ++ [F, G] ++ Δ) (Γ' ++ [F', G'] ++ Δ') := by
      simpa [List.append_assoc] using mg.append ((mF.append mG).append md)
    simpa [List.append_assoc] using LKeProofTree.onePremise
      (.exchangeLeft Γ' F' G' Δ' Λ) (ih mask)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Rebuild a binary rule using recursive consequent-projection callbacks. -/
def two {L : Language} (A B : FormulaN L)
    {prem1 prem2 conc : Sequent L} (rule : FOLKStep2 prem1 prem2 conc)
    (ih1 : ∀ {out}, Mask A B prem1.antecedent out → LKeProofTree (Sequent.mk out prem1.succedent))
    (ih2 : ∀ {out}, Mask A B prem2.antecedent out → LKeProofTree (Sequent.mk out prem2.succedent))
    {out} (m : Mask A B conc.antecedent out) :
    LKeProofTree (Sequent.mk out conc.succedent) := by
  cases rule with
  | cut F Γ Δ Λ Θ =>
    obtain ⟨Γ', Λ', ⟨mg, ml⟩, rfl⟩ := m.split Γ Λ
    exact .twoPremise (.cut F Γ' Δ Λ' Θ) (ih1 mg) (ih2 (.keep F ml))
  | andRight F G Γ Δ => exact .twoPremise (.andRight F G out Δ) (ih1 m) (ih2 m)
  | orLeft F G Γ Δ =>
    cases m with
    | keep _ m => exact .twoPremise (.orLeft F G _ Δ) (ih1 (.keep F m)) (ih2 (.keep G m))
  | implLeft F G Γ Δ Λ Θ =>
    cases m with
    | keep _ m =>
      obtain ⟨Γ', Λ', ⟨mg, ml⟩, rfl⟩ := m.split Γ Λ
      exact .twoPremise (.implLeft F G Γ' Δ Λ' Θ) (ih1 mg) (ih2 (.keep G ml))
    | project m =>
      obtain ⟨Γ', Λ', ⟨mg, ml⟩, rfl⟩ := m.split Γ Λ
      let q1 := ih2 (.keep B ml)
      let q2 := lkeWeakenContexts Γ' Δ (B :: Λ') Θ q1
      have q3 : LKeProofTree (Sequent.mk ([] ++ Γ' ++ [B] ++ Λ') (Θ ++ Δ)) := by
        simpa using q2.val
      let q4 := lkeMoveLeftToFront [] Γ' Λ' (Θ ++ Δ) B q3
      have q5 : LKeProofTree (Sequent.mk (B :: (Γ' ++ Λ')) ([] ++ Θ ++ Δ ++ [])) := by
        simpa using q4.val
      simpa using blockRight [] Θ Δ [] (B :: (Γ' ++ Λ')) q5

-- ATTACH-BLOCKER: termination suffix
/-- Replace selected implication assumptions by structural recursion on a proof tree. -/
def invert {L : Language} (A B : FormulaN L)
    {s : Sequent L} (T : LKeProofTree s) {out : List (FormulaN L)}
    (m : Mask A B s.antecedent out) : LKeProofTree (Sequent.mk out s.succedent) :=
  match T with
  | .axiom_ s hAx => by
    cases s with
    | mk Γ Δ =>
      cases m with
      | nil => exact False.elim (by obtain ⟨F, h, _⟩ := hAx; cases h)
      | keep F m =>
        rename_i xs ys
        have h : Δ = [F] ∧ xs = [] := by
          obtain ⟨G, hΓ, hΔ⟩ := hAx
          simp only [Sequent.antecedent, Sequent.succedent, List.cons.injEq] at hΓ hΔ
          exact ⟨hΔ.trans (congrArg (fun x => [x]) hΓ.1.symm), hΓ.2⟩
        rcases h with ⟨rfl, h⟩
        cases h; cases m
        exact .axiom_ _ ⟨F, rfl, rfl⟩
      | project m =>
        rename_i xs ys
        have h : Δ = [FormulaN.impl A B] ∧ xs = [] := by
          obtain ⟨G, hΓ, hΔ⟩ := hAx
          simp only [Sequent.antecedent, Sequent.succedent, List.cons.injEq] at hΓ hΔ
          exact ⟨hΔ.trans (congrArg (fun x => [x]) hΓ.1.symm), hΓ.2⟩
        rcases h with ⟨rfl, h⟩
        cases h; cases m
        exact .onePremise (.implRight A B [B] [])
          (.onePremise (.weakenLeft A [B] [B]) (.axiom_ _ ⟨B, rfl, rfl⟩))
  | .eqAxiom hL ax => by
    have ha : ∀ F ∈ (ax.toSequent hL).antecedent, F.isAtomic := by
      cases ax <;> simp [LKeEqualityAxiom.toSequent, List.mem_map, FormulaN.isAtomic]
      intro F hF
      rcases hF with ⟨i, rfl⟩ | rfl <;> rfl
    have he := m.atomicEq ha
    subst out
    exact .eqAxiom hL ax
  | .onePremise rule sub => one A B rule (fun {_} m => invert A B sub m) m
  | .twoPremise rule sub1 sub2 => two A B rule
      (fun {_} m => invert A B sub1 m) (fun {_} m => invert A B sub2 m) m
termination_by structural T

end ImplLeftProjection
end LCS.CutElim.LKe.Equivalence
end

