import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.Herbrand.NNFHauptsatz.Equality

section
namespace LCS.Herbrand.SHGTheorem.Herbrand
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.SHGTheorem
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.Equality
open LCS.Herbrand.SharpenedHauptsatz
open LCS.CutElim.Hauptsatz
open LCS.Herbrand.PrenexForm
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae

/-- A term paired with evidence that it has no free variables. -/
abbrev ClosedTerm (L : Language) :=
  {t : Term L // Term.isClosed t}

/-- A partial map from proof eigenvariables to already-closed terms.
The chronological lower-path fold extends this map only after the
corresponding exact existential-left occurrence is crossed. -/
structure ClosedEigenvarMap (L : Language) where
  lookup : Nat → Option (ClosedTerm L)

def ClosedEigenvarMap.empty {L : Language} :
    ClosedEigenvarMap L :=
  ⟨fun _ => none⟩

def ClosedEigenvarMap.insert {L : Language}
    (eigenMap : ClosedEigenvarMap L) (x : Nat)
    (t : ClosedTerm L) : ClosedEigenvarMap L :=
  ⟨fun y => if y = x then some t else eigenMap.lookup y⟩

theorem ClosedEigenvarMap.lookup_insert_self
    {L : Language} (eigenMap : ClosedEigenvarMap L)
    (x : Nat) (t : ClosedTerm L) :
    (eigenMap.insert x t).lookup x = some t := by
  simp [ClosedEigenvarMap.insert]

theorem ClosedEigenvarMap.lookup_insert_of_ne
    {L : Language} (eigenMap : ClosedEigenvarMap L)
    (x y : Nat) (t : ClosedTerm L) (hyx : y ≠ x) :
    (eigenMap.insert x t).lookup y = eigenMap.lookup y := by
  simp [ClosedEigenvarMap.insert, hyx]

/-- Close every unprotected variable using the current eigenvariable
map, with the supplied seed as the explicit fallback.  Variables in
`bound` are binder-protected and remain variables. -/
def closeBaseTermAt {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (bound : List Nat) : Term L → Term L
  | .var x =>
      if x ∈ bound then
        .var x
      else
        match eigenMap.lookup x with
        | some t => t.1
        | none => seed.1
  | .const c => .const c
  | .func f ts =>
      .func f (fun i =>
        closeBaseTermAt seed eigenMap bound (ts i))

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.ClosedSubstitution, LCS.Herbrand.SHGTheorem.Herbrand.Provenance, LCS.Herbrand.SHGTheorem.Herbrand.ScopeAndPurity
/-- Close a standalone Skolem-language term with the current
chronological eigenvariable map and the explicit seed fallback. -/
def closeSkolemTermWithSeed {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (t : Term L) : Term L :=
  closeBaseTermAt seed eigenMap [] t

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.ClosedSubstitution
/-- Every variable retained by term normalization is protected by
the enclosing binder list. -/
theorem closeBaseTermAt_fv_bound {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (bound : List Nat) (t : Term L) :
    ∀ y, y ∈ termFV (closeBaseTermAt seed eigenMap bound t) →
      y ∈ bound := by
  induction t with
  | var x =>
      intro y hy
      by_cases hx : x ∈ bound
      · have hyx : y = x := by
          simpa [closeBaseTermAt, hx, termFV] using hy
        simpa [hyx] using hx
      · cases hMap : eigenMap.lookup x with
        | none =>
            have hClosed := seed.2
            unfold Term.isClosed at hClosed
            simp only [closeBaseTermAt, if_neg hx, hMap] at hy
            rw [hClosed] at hy
            exact hy.elim
        | some t =>
            have hClosed := t.2
            unfold Term.isClosed at hClosed
            simp only [closeBaseTermAt, if_neg hx, hMap] at hy
            rw [hClosed] at hy
            exact hy.elim
  | const _ =>
      intro y hy
      exact hy.elim
  | func f ts ih =>
      intro y hy
      simp only [closeBaseTermAt, termFV] at hy
      obtain ⟨i, hi⟩ := hy
      exact ih i y hi

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.Provenance, LCS.Herbrand.SHGTheorem.Herbrand.ScopeAndPurity
/-- Standalone term normalization is closed. -/
theorem closeSkolemTermWithSeed_isClosed {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (t : Term L) :
    Term.isClosed (closeSkolemTermWithSeed seed eigenMap t) := by
  unfold Term.isClosed closeSkolemTermWithSeed
  ext y
  constructor
  · intro hy
    have hBound :=
      closeBaseTermAt_fv_bound seed eigenMap [] t y hy
    exact (List.not_mem_nil hBound).elim
  · intro hy
    exact hy.elim

end LCS.Herbrand.SHGTheorem.Herbrand
end
