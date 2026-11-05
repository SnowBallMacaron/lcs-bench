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
import LCS.CutElim.LKe.Equivalence.Normalization
import Attach
import LCS.CutElim.LKe.Equivalence.AtomicTranslation.ProofsStamp

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

/-- The consequent projection of a selected implication assumption,
computed by structural recursion and context exchange. -/
def lkeInvertImplLeftConsequent {L : Language} (A B : FormulaN L)
    (Γ Λ Δ : List (FormulaN L))
    (T : LKeProofTree (Sequent.mk (Γ ++ [FormulaN.impl A B] ++ Λ) Δ)) :
    LKeProofTree (Sequent.mk ([B] ++ Γ ++ Λ) Δ) := by
  let q := ImplLeftProjection.invert A B T
    (((ImplLeftProjection.Mask.refl Γ).append (.project .nil)).append
      (ImplLeftProjection.Mask.refl Λ))
  exact (lkeMoveLeftToFront [] Γ Λ Δ B q).val

example {L : Language} (A B : FormulaN L) :
    lkeInvertImplLeftConsequent A B [] [] [FormulaN.impl A B]
      (.axiom_ _ ⟨FormulaN.impl A B, rfl, rfl⟩) =
    LKeProofTree.onePremise (.implRight A B [B] [])
      (.onePremise (.weakenLeft A [B] [B])
        (.axiom_ _ ⟨B, rfl, rfl⟩)) := rfl

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
namespace ImplAntecedentProjection

/-- Select implication assumptions to remove, recording their antecedents in order. -/
inductive Mask {L : Language} (A B : FormulaN L) :
    List (FormulaN L) → List (FormulaN L) → List (FormulaN L) → Type where
  | nil : Mask A B [] [] []
  | keep (F : FormulaN L) {xs ys es} (tail : Mask A B xs ys es) :
      Mask A B (F :: xs) (F :: ys) es
  | project {xs ys es} (tail : Mask A B xs ys es) :
      Mask A B (FormulaN.impl A B :: xs) ys (A :: es)

/-- The occurrence selection that retains every assumption. -/
def Mask.refl {L : Language} {A B : FormulaN L} :
    (xs : List (FormulaN L)) → Mask A B xs xs []
  | [] => .nil
  | F :: xs => .keep F (Mask.refl xs)

/-- Combine occurrence selections and their emitted formulas. -/
def Mask.append {L : Language} {A B : FormulaN L} {xs ys es xs' ys' es'}
    (p : Mask A B xs ys es) (q : Mask A B xs' ys' es') :
    Mask A B (xs ++ xs') (ys ++ ys') (es ++ es') :=
  match p with
  | .nil => q
  | .keep F p => .keep F (p.append q)
  | .project p => .project (p.append q)

/-- Split both the retained and emitted contexts at a source-context boundary. -/
def Mask.split {L : Language} {A B : FormulaN L}
    (xs zs : List (FormulaN L)) {ys es} (m : Mask A B (xs ++ zs) ys es) :
    Σ ys₁ ys₂ es₁ es₂,
      {_p : Mask A B xs ys₁ es₁ × Mask A B zs ys₂ es₂ //
        ys = ys₁ ++ ys₂ ∧ es = es₁ ++ es₂} := by
  cases xs with
  | nil => exact ⟨[], ys, [], es, ⟨.nil, m⟩, rfl, rfl⟩
  | cons F xs =>
    cases m with
    | keep F m =>
      obtain ⟨ys₁, ys₂, es₁, es₂, ⟨p, q⟩, hy, he⟩ := m.split xs zs
      exact ⟨F :: ys₁, ys₂, es₁, es₂, ⟨.keep F p, q⟩,
        by simp [hy], he⟩
    | project m =>
      obtain ⟨ys₁, ys₂, es₁, es₂, ⟨p, q⟩, hy, he⟩ := m.split xs zs
      exact ⟨ys₁, ys₂, A :: es₁, es₂, ⟨.project p, q⟩,
        hy, by simp [he]⟩
termination_by structural xs

/-- Every emitted formula is the antecedent of the selected implication. -/
theorem Mask.emitted {L : Language} {A B : FormulaN L} {xs ys es}
    (m : Mask A B xs ys es) : es = List.replicate es.length A := by
  induction m with
  | nil => rfl
  | keep _ _ ih => exact ih
  | project _ ih => simpa only [List.length_cons, List.replicate_succ] using congrArg (List.cons A) ih

/-- Retained assumptions and emitted antecedents inherit eigenvariable freshness. -/
theorem Mask.fresh {L : Language} {A B : FormulaN L} {xs ys es}
    (m : Mask A B xs ys es) (x : Nat)
    (h : ∀ F ∈ xs, x ∉ formulaFVN F) :
    (∀ F ∈ ys, x ∉ formulaFVN F) ∧ (∀ F ∈ es, x ∉ formulaFVN F) := by
  induction m with
  | nil => simp
  | keep F m ih =>
    obtain ⟨hy, he⟩ := ih (fun G hG => h G (List.mem_cons_of_mem _ hG))
    constructor
    · intro G hG
      rcases List.mem_cons.mp hG with rfl | hG
      · exact h _ List.mem_cons_self
      · exact hy G hG
    · exact he
  | project m ih =>
    obtain ⟨hy, he⟩ := ih (fun G hG => h G (List.mem_cons_of_mem _ hG))
    constructor
    · exact hy
    · intro G hG
      rcases List.mem_cons.mp hG with rfl | hG
      · exact fun hx => h _ List.mem_cons_self (Or.inl hx)
      · exact he G hG

/-- Atomic assumptions are retained and emit no formulas. -/
theorem Mask.atomicEq {L : Language} {A B : FormulaN L} {xs ys es}
    (m : Mask A B xs ys es) (h : ∀ F ∈ xs, F.isAtomic) : ys = xs ∧ es = [] := by
  induction m with
  | nil => exact ⟨rfl, rfl⟩
  | keep F m ih =>
    obtain ⟨hy, he⟩ := ih (fun G hG => h G (List.mem_cons_of_mem _ hG))
    exact ⟨congrArg (List.cons F) hy, he⟩
  | project m ih =>
    have hf := h _ List.mem_cons_self
    simp [FormulaN.isAtomic] at hf

/-- Rebuild a unary rule after removing the selected implication assumptions. -/
def one {L : Language} (A B : FormulaN L)
    {prem conc : Sequent L} (rule : FOLKStep1 prem conc)
    (ih : ∀ {out es}, Mask A B prem.antecedent out es →
      LKeProofTree (Sequent.mk out (prem.succedent ++ es)))
    {out es} (m : Mask A B conc.antecedent out es) :
    LKeProofTree (Sequent.mk out (conc.succedent ++ es)) := by
  cases rule with
  | weakenRight F Γ Δ =>
    let q := LKeProofTree.onePremise (.weakenRight F out (Δ ++ es)) (ih m)
    simpa using (lkeContractContexts.rightFront Δ es [] out F (by simpa using q)).val
  | contractRight F Γ Δ =>
    let q := ImplLeftProjection.blockRight Δ [F, F] es [] out (by simpa using ih m)
    let r := LKeProofTree.onePremise (.contractRight F out (Δ ++ es)) (by simpa using q)
    simpa using (lkeContractContexts.rightFront Δ es [] out F (by simpa using r)).val
  | exchangeRight Γ Δ F G Λ =>
    simpa [List.append_assoc] using LKeProofTree.onePremise
      (.exchangeRight out Δ F G (Λ ++ es)) (by simpa [List.append_assoc] using ih m)
  | orRightL F G Γ Δ =>
    let q := lkeMoveRightToEnd Δ es [] out F (by simpa using ih m)
    let r := LKeProofTree.onePremise (.orRightL F G out (Δ ++ es)) (by simpa using q.val)
    simpa using (lkeContractContexts.rightFront Δ es [] out (FormulaN.disj F G) (by simpa using r)).val
  | orRightR F G Γ Δ =>
    let q := lkeMoveRightToEnd Δ es [] out G (by simpa using ih m)
    let r := LKeProofTree.onePremise (.orRightR F G out (Δ ++ es)) (by simpa using q.val)
    simpa using (lkeContractContexts.rightFront Δ es [] out (FormulaN.disj F G) (by simpa using r)).val
  | exRight t x F Γ Δ hf =>
    let q := lkeMoveRightToEnd Δ es [] out (formulaSubstN F t x) (by simpa using ih m)
    let r := LKeProofTree.onePremise (.exRight t x F out (Δ ++ es) hf) (by simpa using q.val)
    simpa using (lkeContractContexts.rightFront Δ es [] out (FormulaN.ex x F) (by simpa using r)).val
  | negRight F Γ Δ =>
    let r := LKeProofTree.onePremise (.negRight F out (Δ ++ es)) (ih (.keep F m))
    simpa using (lkeContractContexts.rightFront Δ es [] out (FormulaN.neg F) (by simpa using r)).val
  | implRight F G Γ Δ =>
    let q := lkeMoveRightToEnd Δ es [] (F :: out) G (by simpa using ih (.keep F m))
    let r := LKeProofTree.onePremise (.implRight F G out (Δ ++ es)) (by simpa using q.val)
    simpa using (lkeContractContexts.rightFront Δ es [] out (FormulaN.impl F G) (by simpa using r)).val
  | allRight y x F Γ Δ fresh hf =>
    have hm := m.fresh y (fun H hH => fresh H (List.mem_append_left _ hH))
    have hfresh : ∀ H ∈ out ++ ((Δ ++ es) ++ [FormulaN.all x F]), y ∉ formulaFVN H := by
      intro H hH
      simp only [List.mem_append, List.mem_singleton] at hH
      rcases hH with hH | ((hH | hH) | hH)
      · exact hm.1 H hH
      · exact fresh H (by simp [hH])
      · exact hm.2 H hH
      · subst H; exact fresh _ (by simp)
    let q := lkeMoveRightToEnd Δ es [] out (formulaSubstN F (Term.var y) x)
      (by simpa using ih m)
    let r := LKeProofTree.onePremise (.allRight y x F out (Δ ++ es) hfresh hf)
      (by simpa using q.val)
    simpa using (lkeContractContexts.rightFront Δ es [] out (FormulaN.all x F) (by simpa using r)).val
  | weakenLeft F Γ Δ =>
    cases m with
    | keep F m => exact .onePremise (.weakenLeft F _ _) (ih m)
    | project m =>
      let q := LKeProofTree.onePremise (.weakenRight A _ _) (ih m)
      simpa using (lkeContractContexts.rightFront Δ _ [] _ A (by simpa using q)).val
  | contractLeft F Γ Δ =>
    cases m with
    | keep F m => exact .onePremise (.contractLeft F _ _) (ih (.keep F (.keep F m)))
    | project m =>
      rename_i es
      let q := ImplLeftProjection.blockRight Δ [A, A] es [] out
        (by simpa using ih (.project (.project m)))
      let r := LKeProofTree.onePremise (.contractRight A out (Δ ++ es)) (by simpa using q)
      simpa using (lkeContractContexts.rightFront Δ es [] out A (by simpa using r)).val
  | andLeftL F G Γ Δ =>
    cases m with
    | keep _ m => exact .onePremise (.andLeftL F G _ _) (ih (.keep F m))
  | andLeftR F G Γ Δ =>
    cases m with
    | keep _ m => exact .onePremise (.andLeftR F G _ _) (ih (.keep G m))
  | negLeft F Γ Δ =>
    cases m with
    | keep _ m =>
      let q := lkeMoveRightToEnd Δ _ [] _ F (by simpa using ih m)
      exact .onePremise (.negLeft F _ _) (by simpa using q.val)
  | allLeft t x F Γ Δ hf =>
    cases m with
    | keep _ m => exact .onePremise (.allLeft t x F _ _ hf) (ih (.keep (formulaSubstN F t x) m))
  | exLeft y x F Γ Δ fresh hf =>
    cases m with
    | keep _ m =>
      have hm := (Mask.keep (FormulaN.ex x F) m).fresh y
        (fun H hH => fresh H (List.mem_append_left _ hH))
      refine .onePremise (.exLeft y x F _ _ ?_ hf)
        (ih (.keep (formulaSubstN F (Term.var y) x) m))
      intro H hH
      rcases List.mem_append.mp hH with hH | hH
      · exact hm.1 H hH
      · rcases List.mem_append.mp hH with hH | hH
        · exact fresh H (List.mem_append_right _ hH)
        · exact hm.2 H hH
  | exchangeLeft Γ F G Δ Λ =>
    obtain ⟨Γ', tail, eg, et, ⟨mg, mt⟩, hout, hes⟩ := Mask.split Γ ([G, F] ++ Δ)
      (by simpa [List.append_assoc] using m)
    obtain ⟨mid, Δ', em, ed, ⟨mm, md⟩, htail, het⟩ := mt.split [G, F] Δ
    subst out; subst es; subst tail; subst et
    cases mm with
    | keep G mm =>
      cases mm with
      | keep F mm =>
        cases mm
        have mask := mg.append ((Mask.keep F (.keep G .nil)).append md)
        simpa [List.append_assoc] using LKeProofTree.onePremise
          (.exchangeLeft Γ' F G Δ' (Λ ++ (eg ++ ed))) (ih (by simpa [List.append_assoc] using mask))
      | project mm =>
        cases mm
        have mask := mg.append ((Mask.project (.keep G .nil)).append md)
        simpa [List.append_assoc] using ih (by simpa [List.append_assoc] using mask)
    | project mm =>
      cases mm with
      | keep F mm =>
        cases mm
        have mask := mg.append ((Mask.keep F (.project .nil)).append md)
        simpa [List.append_assoc] using ih (by simpa [List.append_assoc] using mask)
      | project mm =>
        cases mm
        have mask := mg.append ((Mask.project (.project .nil)).append md)
        simpa [List.append_assoc] using ih (by simpa [List.append_assoc] using mask)

/-- Move an antecedent block to the right of the following context. -/
def blockLeft {L : Language} (pre block mid post Δ : List (FormulaN L))
    (T : LKeProofTree (Sequent.mk (pre ++ block ++ mid ++ post) Δ)) :
    LKeProofTree (Sequent.mk (pre ++ mid ++ block ++ post) Δ) := by
  cases block with
  | nil => simpa using T
  | cons F rest =>
    let q := blockLeft (pre ++ [F]) rest mid post Δ (by simpa using T)
    simpa using (lkeContractContexts.leftBack pre mid (rest ++ post) Δ F
      (by simpa using q)).val
termination_by structural block

/-- Rebuild a binary rule after removing selected implication assumptions. -/
def two {L : Language} (A B : FormulaN L)
    {prem1 prem2 conc : Sequent L} (rule : FOLKStep2 prem1 prem2 conc)
    (ih1 : ∀ {out es}, Mask A B prem1.antecedent out es → LKeProofTree (Sequent.mk out (prem1.succedent ++ es)))
    (ih2 : ∀ {out es}, Mask A B prem2.antecedent out es → LKeProofTree (Sequent.mk out (prem2.succedent ++ es)))
    {out es} (m : Mask A B conc.antecedent out es) :
    LKeProofTree (Sequent.mk out (conc.succedent ++ es)) := by
  cases rule with
  | cut F Γ Δ Λ Θ =>
    obtain ⟨Γ', Λ', eg, el, ⟨mg, ml⟩, rfl, rfl⟩ := m.split Γ Λ
    let q := lkeMoveRightToEnd Δ eg [] Γ' F (by simpa using ih1 mg)
    let r := LKeProofTree.twoPremise (.cut F Γ' (Δ ++ eg) Λ' (Θ ++ el))
      (by simpa using q.val) (ih2 (.keep F ml))
    simpa [List.append_assoc] using ImplLeftProjection.blockRight Δ eg Θ el (Γ' ++ Λ')
      (by simpa [List.append_assoc] using r)
  | andRight F G Γ Δ =>
    let q1 := lkeMoveRightToEnd Δ es [] out F (by simpa using ih1 m)
    let q2 := lkeMoveRightToEnd Δ es [] out G (by simpa using ih2 m)
    let r := LKeProofTree.twoPremise (.andRight F G out (Δ ++ es))
      (by simpa using q1.val) (by simpa using q2.val)
    simpa using (lkeContractContexts.rightFront Δ es [] out (FormulaN.conj F G) (by simpa using r)).val
  | orLeft F G Γ Δ =>
    cases m with
    | keep _ m => exact .twoPremise (.orLeft F G _ _) (ih1 (.keep F m)) (ih2 (.keep G m))
  | implLeft F G Γ Δ Λ Θ =>
    cases m with
    | keep _ m =>
      obtain ⟨Γ', Λ', eg, el, ⟨mg, ml⟩, rfl, rfl⟩ := m.split Γ Λ
      let q := lkeMoveRightToEnd Δ eg [] Γ' F (by simpa using ih1 mg)
      let r := LKeProofTree.twoPremise (.implLeft F G Γ' (Δ ++ eg) Λ' (Θ ++ el))
        (by simpa using q.val) (ih2 (.keep G ml))
      simpa [List.append_assoc] using ImplLeftProjection.blockRight Δ eg Θ el
        (FormulaN.impl F G :: (Γ' ++ Λ')) (by simpa [List.append_assoc] using r)
    | project m =>
      obtain ⟨Γ', Λ', eg, el, ⟨mg, ml⟩, rfl, rfl⟩ := m.split Γ Λ
      let q := lkeWeakenContexts Λ' (Θ ++ el) Γ' ((Δ ++ [A]) ++ eg) (ih1 mg)
      let r := blockLeft [] Λ' Γ' [] (((Δ ++ [A]) ++ eg) ++ (Θ ++ el))
        (by simpa using q.val)
      let u := ImplLeftProjection.blockRight (Δ ++ [A]) eg Θ el (Γ' ++ Λ')
        (by simpa [List.append_assoc] using r)
      simpa [List.append_assoc] using (lkeMoveRightToEnd Δ Θ (eg ++ el) (Γ' ++ Λ') A
        (by simpa [List.append_assoc] using u)).val

/-- Remove selected implication assumptions and emit their antecedents by recursion on the proof. -/
def invert {L : Language} (A B : FormulaN L)
    {s : Sequent L} (T : LKeProofTree s) {out es : List (FormulaN L)}
    (m : Mask A B s.antecedent out es) : LKeProofTree (Sequent.mk out (s.succedent ++ es)) :=
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
        rename_i xs es
        have h : Δ = [FormulaN.impl A B] ∧ xs = [] := by
          obtain ⟨G, hΓ, hΔ⟩ := hAx
          simp only [Sequent.antecedent, Sequent.succedent, List.cons.injEq] at hΓ hΔ
          exact ⟨hΔ.trans (congrArg (fun x => [x]) hΓ.1.symm), hΓ.2⟩
        rcases h with ⟨rfl, h⟩
        cases h; cases m
        exact .onePremise (.exchangeRight [] [] A (FormulaN.impl A B) [])
          (.onePremise (.implRight A B [] [A])
            (.onePremise (.weakenRight B [A] [A]) (.axiom_ _ ⟨A, rfl, rfl⟩)))
  | .eqAxiom hL ax => by
    have ha : ∀ F ∈ (ax.toSequent hL).antecedent, F.isAtomic := by
      cases ax <;> simp [LKeEqualityAxiom.toSequent, List.mem_map, FormulaN.isAtomic]
      intro F hF
      rcases hF with ⟨i, rfl⟩ | rfl <;> rfl
    obtain ⟨he, hx⟩ := m.atomicEq ha
    subst out; subst es
    simpa using LKeProofTree.eqAxiom hL ax
  | .onePremise rule sub => one A B rule (fun {_ _} m => invert A B sub m) m
  | .twoPremise rule sub1 sub2 => two A B rule
      (fun {_ _} m => invert A B sub1 m) (fun {_ _} m => invert A B sub2 m) m
termination_by structural T

end ImplAntecedentProjection
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

/-- The antecedent projection of an implication assumption, computed by an occurrence mask. -/
def lkeInvertImplLeftAntecedent {L : Language} (A B : FormulaN L)
    (Γ Λ Δ : List (FormulaN L))
    (T : LKeProofTree (Sequent.mk (Γ ++ [FormulaN.impl A B] ++ Λ) Δ)) :
    LKeProofTree (Sequent.mk (Γ ++ Λ) (Δ ++ [A])) := by
  let m := ((ImplAntecedentProjection.Mask.refl (A := A) (B := B) Γ).append
    (.project .nil)).append (ImplAntecedentProjection.Mask.refl Λ)
  simpa using ImplAntecedentProjection.invert A B T m

example {L : Language} (A B : FormulaN L) :
    lkeInvertImplLeftAntecedent A B [] [] [FormulaN.impl A B]
      (.axiom_ _ ⟨FormulaN.impl A B, rfl, rfl⟩) =
    LKeProofTree.onePremise (.exchangeRight [] [] A (FormulaN.impl A B) [])
      (.onePremise (.implRight A B [] [A])
        (.onePremise (.weakenRight B [A] [A]) (.axiom_ _ ⟨A, rfl, rfl⟩))) := rfl


/-- Invert a selected implication assumption into its antecedent and consequent projections. -/
def lkeInvertImplLeft {L : Language} (A B : FormulaN L)
    (Γ Λ Δ : List (FormulaN L))
    (T : LKeProofTree (Sequent.mk (Γ ++ [FormulaN.impl A B] ++ Λ) Δ)) :
    LKeProofTree (Sequent.mk (Γ ++ Λ) (Δ ++ [A])) ×
      LKeProofTree (Sequent.mk ([B] ++ Γ ++ Λ) Δ) :=
  ⟨lkeInvertImplLeftAntecedent A B Γ Λ Δ T,
    lkeInvertImplLeftConsequent A B Γ Λ Δ T⟩

/-- Both implication-inversion projections preserve the atomic-cut condition. -/
theorem lkeInvertImplLeft_allCutsAtomic {L : Language} (A B : FormulaN L)
    (Γ Λ Δ : List (FormulaN L))
    (T : LKeProofTree (Sequent.mk (Γ ++ [FormulaN.impl A B] ++ Λ) Δ))
    (hT : lkeAllCutsAtomic T) :
    lkeAllCutsAtomic (lkeInvertImplLeft A B Γ Λ Δ T).1 ∧
      lkeAllCutsAtomic (lkeInvertImplLeft A B Γ Λ Δ T).2 := by
  -- REPAIR(T6-73e): proof pending
  sorry

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

/-- Atomic cuts in every input and atomic splice formulas give an atomic-cut result. -/
theorem lkeAtomicCongruenceSplice_allCutsAtomic {L : Language}
    (atoms : List (FormulaN L)) (C : FormulaN L) (Γ Δ : List (FormulaN L))
    (proofs : (i : Fin atoms.length) → LKeProofTree (Sequent.mk Γ (Δ ++ [atoms[i]])))
    (ax : LKeProofTree (Sequent.mk atoms [C]))
    (continuation : LKeProofTree (Sequent.mk (C :: Γ) Δ))
    (hAtoms : ∀ A ∈ atoms, A.isAtomic) (hC : C.isAtomic)
    (hProofs : ∀ i, lkeAllCutsAtomic (proofs i))
    (hAx : lkeAllCutsAtomic ax) (hContinuation : lkeAllCutsAtomic continuation) :
    lkeAllCutsAtomic (lkeAtomicCongruenceSplice atoms C Γ Δ proofs ax continuation) := by
  -- REPAIR(T6-73f): proof pending
  sorry

example {L : Language} (hL : L.hasEquality = true) (t : Term L) :
    lkeAtomicCongruenceSplice [] (FormulaN.eq_ hL t t) [] [FormulaN.eq_ hL t t]
      (fun i => nomatch i) (.eqAxiom hL (.refl t))
      (.axiom_ _ ⟨FormulaN.eq_ hL t t, rfl, rfl⟩) =
    LKeProofTree.twoPremise (.cut (FormulaN.eq_ hL t t) [] [] [] [FormulaN.eq_ hL t t])
      (.eqAxiom hL (.refl t)) (.axiom_ _ ⟨FormulaN.eq_ hL t t, rfl, rfl⟩) := rfl


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

/-- The reflexivity simulation preserves the property that every cut is an equation. -/
theorem geqRefl_to_lkeAtomicCut_allCutsEquational {L : Language}
    (hL : L.hasEquality = true) (t : Term L) (Γ Δ : List (FormulaN L))
    (premise : LKeProofTree
      (Sequent.mk ([FormulaN.eq_ hL t t] ++ Γ) Δ)) :
    lkeAllCutsEquational (geqRefl_to_lkeAtomicCut hL t Γ Δ premise) ↔
      lkeAllCutsEquational premise := by
  simp [geqRefl_to_lkeAtomicCut, LKeProofTree.cut, lkeAllCutsEquational]

example {L : Language} (hL : L.hasEquality = true) (t : Term L) :
    geqRefl_to_lkeAtomicCut hL t [] [FormulaN.eq_ hL t t]
      (.axiom_ _ ⟨FormulaN.eq_ hL t t, rfl, rfl⟩) =
    LKeProofTree.twoPremise (.cut (FormulaN.eq_ hL t t) [] [] []
      [FormulaN.eq_ hL t t]) (.eqAxiom hL (.refl t))
      (.axiom_ _ ⟨FormulaN.eq_ hL t t, rfl, rfl⟩) := rfl

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

-- Helper: folkCutFreeProvable implies LKe-provable without essential cuts
theorem folkCutFree_implies_lkeNoEssentialCuts {L : Language}
    (s : Sequent L) (h : folkCutFreeProvable s) :
    lkeProvableWithoutEssentialCuts s := by
-- BEGIN PROOF
  obtain ⟨t, hcf⟩ := h
  exact ⟨.lk t,
    (lkeAllCutsAtomic_lk t).2
      (cutFree_implies_allCutsAtomic t hcf)⟩

attribute [blueprint "chap6__theorem_6_3_1"] LKeAtomicProofTree

end LCS.CutElim.LKe.Equivalence
end
