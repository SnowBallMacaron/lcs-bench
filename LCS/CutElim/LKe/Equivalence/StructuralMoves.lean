import LCS.Item
import LCS.Util
import LCS.CutElim.LKe
import LCS.CutElim.CompletenessBridge
import LCS.FirstOrder.Equality.Completeness
import LCS.FirstOrder.Semantics.Subformulae
import LCS.CutElim.LKe.Equivalence.AtomicCuts

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
