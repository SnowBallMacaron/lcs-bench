import LCS.FirstOrder.Gentzen.Hintikka.Model

section

namespace LCS.FirstOrder.Gentzen.Hintikka

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.SemanticsN.Substitution

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Gentzen.SignedFormulae

open LCS.FirstOrder.SyntaxN.Variables

helper /-- Lemma 5.4.5 (companion): If H is a term algebra and every free
variable x of term t has Term.var x ∈ H, then t ∈ H. Proved by
structural induction on terms: variables are in H by assumption,
constants by closedConst, and function applications by closedFunc
with the induction hypothesis. -/
theorem termInH {L : Language} {H : Set (Term L)}
    (hTA : IsTermAlgebra L H) (t : Term L)
    (hvars : ∀ x, x ∈ termFV t → Term.var x ∈ H) : t ∈ H := by
-- BEGIN PROOF
  induction t with
  | var x => exact hvars x rfl
  | const c => exact hTA.closedConst c
  | func f ts ih =>
    exact hTA.closedFunc f ts (fun i => ih i (fun x hx => hvars x ⟨i, hx⟩))



helper /-- The sequent convention gives the set-wide convention for its formulae. -/
theorem setCrossNoFreeBound_of_sequent {L : Language} (seq : Sequent L)
    (h : crossNoFreeBound seq) :
    setCrossNoFreeBound (fun A => A ∈ seq.antecedent ++ seq.succedent) := h

helper /-- crossNoFreeBound implies noFreeBound.

UNFAITHFUL — TO REMOVE with `noFreeBound`: this bridge lemma only
exists to convert the faithful §5.4.7 standing assumption into the
weaker per-formula variant consumed by the unfaithful Thm 5.5.1
scaffolding. Remove together with `noFreeBound`. -/
theorem crossNoFreeBound_implies_noFreeBound {L : Language} (seq : Sequent L)
    (h : crossNoFreeBound seq) : noFreeBound seq := by
-- BEGIN PROOF
  intro A hA x ⟨hfv, hbv⟩
  exact h x ⟨A, hA, hfv⟩ A hA hbv





proof_of hintikka_term_closure := by
  intro sf hsf t hocc hfree
  apply termInHOver hTA t
  · cases sf with
    | trueF A =>
      have hsyms := termOccursInFormulaN_symbols A hocc
      exact ⟨fun f hf => ⟨.trueF A, hsf, hsyms.1 f hf⟩,
        fun c hc => ⟨.trueF A, hsf, hsyms.2 c hc⟩⟩
    | falseF A =>
      have hsyms := termOccursInFormulaN_symbols A hocc
      exact ⟨fun f hf => ⟨.falseF A, hsf, hsyms.1 f hf⟩,
        fun c hc => ⟨.falseF A, hsf, hsyms.2 c hc⟩⟩
  · intro x hx
    rcases hfree with hclosed | hvars
    · have hempty : termFV t = ∅ := hclosed
      exact False.elim (show x ∈ (∅ : Set Nat) from hempty ▸ hx)
    · obtain ⟨sf', hsf', hx'⟩ := hvars x hx
      exact h5 sf' hsf' x hx'


















proof_of hintikka_set_satisfiable := ⟨hintikkaStructure H S hHS, identityAssignment H S hHS,
  -- BEGIN PROOF
     hintikka_set_satisfiable_concrete hL H S hHS⟩


end LCS.FirstOrder.Gentzen.Hintikka

end
