import LCS.Item
import LCS.Util
import LCS.CutElim.LKe
import LCS.CutElim.CompletenessBridge
import LCS.FirstOrder.Equality.Completeness
import LCS.FirstOrder.Semantics.Subformulae
import LCS.CutElim.LKe.Equivalence.AtomicCuts
import LCS.CutElim.LKe.Equivalence.StructuralMoves

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

/-- Select succedent occurrences of a conjunction and record their chosen conjunct. -/
inductive Mask {L : Language} (A B : FormulaN L) (pick : Bool) :
    List (FormulaN L) → List (FormulaN L) → Type where
  | nil : Mask A B pick [] []
  | keep (F : FormulaN L) {xs ys} (tail : Mask A B pick xs ys) :
      Mask A B pick (F :: xs) (F :: ys)
  | project {xs ys} (tail : Mask A B pick xs ys) :
      Mask A B pick (FormulaN.conj A B :: xs) ((if pick then A else B) :: ys)

/-- Leave every formula occurrence unchanged. -/
def Mask.refl {L : Language} {A B : FormulaN L} {pick} :
    (xs : List (FormulaN L)) → Mask A B pick xs xs
  | [] => .nil
  | F :: xs => .keep F (Mask.refl xs)

/-- Concatenate two occurrence selections. -/
def Mask.append {L : Language} {A B : FormulaN L} {pick xs xs' ys ys'}
    (p : Mask A B pick xs xs') (q : Mask A B pick ys ys') :
    Mask A B pick (xs ++ ys) (xs' ++ ys') :=
  match p with
  | .nil => q
  | .keep F p => .keep F (p.append q)
  | .project p => .project (p.append q)

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

/-- Read the resulting formula of a singleton occurrence selection. -/
def Mask.singleton {L : Language} {A B : FormulaN L} {pick F ys}
    (p : Mask A B pick [F] ys) : {G : FormulaN L // ys = [G]} := by
  cases p with
  | keep F p => cases p; exact ⟨F, rfl⟩
  | project p => cases p; exact ⟨if pick then A else B, rfl⟩

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
open LCS.FirstOrder.Equality

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

namespace ImplLeftProjection

/-- Select antecedent implications and replace them by their consequents. -/
inductive Mask {L : Language} (A B : FormulaN L) :
    List (FormulaN L) → List (FormulaN L) → Type where
  | nil : Mask A B [] []
  | keep (F : FormulaN L) {xs ys} (tail : Mask A B xs ys) :
      Mask A B (F :: xs) (F :: ys)
  | project {xs ys} (tail : Mask A B xs ys) :
      Mask A B (FormulaN.impl A B :: xs) (B :: ys)

/-- Leave every antecedent occurrence unchanged. -/
def Mask.refl {L : Language} {A B : FormulaN L}  :
    (xs : List (FormulaN L)) → Mask A B xs xs
  | [] => .nil
  | F :: xs => .keep F (Mask.refl xs)

/-- Concatenate two antecedent occurrence selections. -/
def Mask.append {L : Language} {A B : FormulaN L} {xs xs' ys ys'}
    (p : Mask A B xs xs') (q : Mask A B ys ys') :
    Mask A B (xs ++ ys) (xs' ++ ys') :=
  match p with
  | .nil => q
  | .keep F p => .keep F (p.append q)
  | .project p => .project (p.append q)

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

/-- Read the resulting formula of a singleton selection. -/
def Mask.singleton {L : Language} {A B : FormulaN L} {F ys}
    (p : Mask A B [F] ys) : {G : FormulaN L // ys = [G]} := by
  cases p with
  | keep F p => cases p; exact ⟨F, rfl⟩
  | project p => cases p; exact ⟨B, rfl⟩

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

/-- The antecedent projection of an implication assumption, computed by an occurrence mask. -/
def lkeInvertImplLeftAntecedent {L : Language} (A B : FormulaN L)
    (Γ Λ Δ : List (FormulaN L))
    (T : LKeProofTree (Sequent.mk (Γ ++ [FormulaN.impl A B] ++ Λ) Δ)) :
    LKeProofTree (Sequent.mk (Γ ++ Λ) (Δ ++ [A])) := by
  let m := ((ImplAntecedentProjection.Mask.refl (A := A) (B := B) Γ).append
    (.project .nil)).append (ImplAntecedentProjection.Mask.refl Λ)
  simpa using ImplAntecedentProjection.invert A B T m

/-- Invert a selected implication assumption into its antecedent and consequent projections. -/
def lkeInvertImplLeft {L : Language} (A B : FormulaN L)
    (Γ Λ Δ : List (FormulaN L))
    (T : LKeProofTree (Sequent.mk (Γ ++ [FormulaN.impl A B] ++ Λ) Δ)) :
    LKeProofTree (Sequent.mk (Γ ++ Λ) (Δ ++ [A])) ×
      LKeProofTree (Sequent.mk ([B] ++ Γ ++ Λ) Δ) :=
  ⟨lkeInvertImplLeftAntecedent A B Γ Λ Δ T,
    lkeInvertImplLeftConsequent A B Γ Λ Δ T⟩

end LCS.CutElim.LKe.Equivalence
end
