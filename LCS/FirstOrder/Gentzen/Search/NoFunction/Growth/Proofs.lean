import LCS.FirstOrder.Gentzen.Search.NoFunction.Growth

section

namespace LCS.FirstOrder.Gentzen.Search.NoFunction

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Gentzen.Hintikka



helper /-- Definition 5.4.9 (companion, leaf-level invariant): `LeafBVBelow`
    is monotone in the bound. -/
theorem LeafBVBelow_mono {L : Language} {leaf : Sequent L} {b b' : Nat}
    (h : LeafBVBelow leaf b) (hle : b ≤ b') : LeafBVBelow leaf b' := by
-- BEGIN PROOF
  intro F hF j hj
  exact Nat.lt_of_lt_of_le (h F hF j hj) hle





helper /-- Definition 5.4.9 (companion, discharge): If `∃x A ∈ leaf` and
    `LeafBVBelow leaf bound`, then `BV(A) ⊆ {j : j < bound}`. Used to
    discharge `y ∉ BV(A)` for the fresh eigenvariable `y := availNext`
    in `growLeftExInv`. -/
theorem notBV_A_of_ex_leaf {L : Language} {leaf : Sequent L} {bound : Nat}
    (hLeafBV : LeafBVBelow leaf bound) {x : Nat} {A : FormulaN L}
    (hExIn : FormulaN.ex x A ∈ leaf.antecedent ++ leaf.succedent)
    {y : Nat} (hY : bound ≤ y) :
    y ∉ formulaBVN A := by
-- BEGIN PROOF
  intro hBV
  -- formulaBVN (∃x A) = formulaBVN A ∪ {x}, so y ∈ BV(A) ⇒ y ∈ BV(∃x A).
  have hInBV : y ∈ formulaBVN (FormulaN.ex x A) := Or.inl hBV
  have hlt : y < bound := hLeafBV _ hExIn y hInBV
  exact Nat.not_lt_of_le hY hlt

helper /-- Definition 5.4.9 (companion, discharge): Mirror for `∀x A`. -/
theorem notBV_A_of_all_leaf {L : Language} {leaf : Sequent L} {bound : Nat}
    (hLeafBV : LeafBVBelow leaf bound) {x : Nat} {A : FormulaN L}
    (hAllIn : FormulaN.all x A ∈ leaf.antecedent ++ leaf.succedent)
    {y : Nat} (hY : bound ≤ y) :
    y ∉ formulaBVN A := by
-- BEGIN PROOF
  intro hBV
  have hInBV : y ∈ formulaBVN (FormulaN.all x A) := Or.inl hBV
  have hlt : y < bound := hLeafBV _ hAllIn y hInBV
  exact Nat.not_lt_of_le hY hlt

helper /-- Definition 5.4.9 (companion, tree walker): Walk a `GDeductionTreeExt s`
    applying an extender at every non-axiom leaf. Axiom leaves are
    preserved unchanged. State is threaded through the walk in
    `GDeductionTreeExt.leaves`-order (left-to-right over twoPremise,
    down the only child over onePremise).

    The extender has type:
      `∀ leaf, ¬ isAxiom leaf → SearchState L → GDeductionTreeExt leaf × SearchState L`

    i.e. given a non-axiom leaf and the current state, it produces
    an extension subtree whose conclusion is the leaf (type-enforced)
    together with an updated state. The walker glues these subtrees
    back into the original tree structure using the `onePremise` /
    `twoPremise` constructors.

    Textbook §5.4.9 grow-left / grow-right: "extend every nonaxiom
    leaf of S using the …-rule". The walker is what "every" means:
    it dispatches a per-leaf extender at each leaf that is not
    already an axiom.

    `noncomputable` because it dispatches on `isAxiom`, which uses
    `DecidableEq FormulaN` (classical-propositional). -/
noncomputable def extendAllNonaxiomLeaves {L : Language} {supply : TermStream L}
    (extender : ∀ leaf : Sequent L, ¬ isAxiom leaf → SearchState L supply →
      GDeductionTreeExt leaf × SearchState L supply) :
    {s : Sequent L} → GDeductionTreeExt s → SearchState L supply →
      GDeductionTreeExt s × SearchState L supply
  | _, .leaf s, st =>
      match Classical.propDecidable (isAxiom s) with
      | isTrue _ => (GDeductionTreeExt.leaf s, st)
      | isFalse hne => extender s hne st
  | _, .onePremise rule t, st =>
      let (t', st') := extendAllNonaxiomLeaves extender t st
      (GDeductionTreeExt.onePremise rule t', st')
  | _, .twoPremise rule t1 t2, st =>
      let (t1', st1) := extendAllNonaxiomLeaves extender t1 st
      let (t2', st2) := extendAllNonaxiomLeaves extender t2 st1
      (GDeductionTreeExt.twoPremise rule t1' t2', st2)

helper /-- Definition 5.4.9 (companion, tree walker preservation): If the
    extender preserves the invariant `Inv seq bound` at every state
    update, then the walker also preserves `Inv seq bound`. -/
theorem extendAllNonaxiomLeaves_preserves_Inv {L : Language} {supply : TermStream L}
    {seq : Sequent L} {bound : Nat}
    (extender : ∀ leaf : Sequent L, ¬ isAxiom leaf → SearchState L supply →
      GDeductionTreeExt leaf × SearchState L supply)
    (ext_inv :
      ∀ leaf (hne : ¬ isAxiom leaf) (st : SearchState L supply),
        SearchState.Inv seq bound st →
        SearchState.Inv seq bound (extender leaf hne st).2) :
    ∀ {s : Sequent L} (t : GDeductionTreeExt s) (st : SearchState L supply),
      SearchState.Inv seq bound st →
      SearchState.Inv seq bound
        (extendAllNonaxiomLeaves extender t st).2
  | _, .leaf s, st, hInv => by
      unfold extendAllNonaxiomLeaves
      split
      · exact hInv
      · exact ext_inv s _ st hInv
  | _, .onePremise _ t, st, hInv => by
      unfold extendAllNonaxiomLeaves
      simp only
      exact extendAllNonaxiomLeaves_preserves_Inv extender ext_inv t st hInv
  | _, .twoPremise _ t1 t2, st, hInv => by
      unfold extendAllNonaxiomLeaves
      simp only
      have h1 := extendAllNonaxiomLeaves_preserves_Inv extender ext_inv t1 st hInv
      exact extendAllNonaxiomLeaves_preserves_Inv extender ext_inv t2 _ h1

helper /-- Definition 5.4.9 (companion, tree walker preservation): `availNext`
    is monotone across the walker — it only grows. Useful for
    propagating `LeafFVBelow` with the incremented bound. -/
theorem extendAllNonaxiomLeaves_availNext_mono {L : Language} {supply : TermStream L}
    (extender : ∀ leaf : Sequent L, ¬ isAxiom leaf → SearchState L supply →
      GDeductionTreeExt leaf × SearchState L supply)
    (ext_mono :
      ∀ leaf (hne : ¬ isAxiom leaf) (st : SearchState L supply),
        st.availNext ≤ (extender leaf hne st).2.availNext) :
    ∀ {s : Sequent L} (t : GDeductionTreeExt s) (st : SearchState L supply),
      st.availNext ≤ (extendAllNonaxiomLeaves extender t st).2.availNext
  | _, .leaf s, st => by
      unfold extendAllNonaxiomLeaves
      split
      · exact Nat.le_refl _
      · exact ext_mono s _ st
  | _, .onePremise _ t, st => by
      unfold extendAllNonaxiomLeaves
      simp only
      exact extendAllNonaxiomLeaves_availNext_mono extender ext_mono t st
  | _, .twoPremise _ t1 t2, st => by
      unfold extendAllNonaxiomLeaves
      simp only
      have h1 := extendAllNonaxiomLeaves_availNext_mono extender ext_mono t1 st
      have h2 :=
-- BEGIN PROOF
        extendAllNonaxiomLeaves_availNext_mono extender ext_mono t2
          (extendAllNonaxiomLeaves extender t1 st).2
      exact Nat.le_trans h1 h2















helper /-- `growLeftExInv` preserves `Inv`. -/
theorem growLeftExInv_preserves_Inv {L : Language} {supply : TermStream L}
    {seq : Sequent L} {bound : Nat}
    (x : Nat) (A : FormulaN L) (leaf : Sequent L)
    (hA : FormulaN.ex x A ∈ leaf.antecedent)
    (st : SearchState L supply) (records : BranchRecords L) (hInv : SearchState.Inv seq bound st)
    (hLeafFV : LeafFVBelow supply leaf st.availNext)
    (hLeafBV : LeafBVBelow leaf bound)
    (hLeafBVSub : LeafBVSubsetSeq leaf seq) :
    SearchState.Inv seq bound
      (growLeftExInv x A leaf hA st records hInv hLeafFV hLeafBV hLeafBVSub).2 := by
-- BEGIN PROOF
  unfold growLeftExInv
  simp only
  exact hInv



helper /-- `growRightAllInv` preserves `Inv`. -/
theorem growRightAllInv_preserves_Inv {L : Language} {supply : TermStream L}
    {seq : Sequent L} {bound : Nat}
    (x : Nat) (C : FormulaN L) (leaf : Sequent L)
    (hB : FormulaN.all x C ∈ leaf.succedent)
    (st : SearchState L supply) (records : BranchRecords L) (hInv : SearchState.Inv seq bound st)
    (hLeafFV : LeafFVBelow supply leaf st.availNext)
    (hLeafBV : LeafBVBelow leaf bound)
    (hLeafBVSub : LeafBVSubsetSeq leaf seq) :
    SearchState.Inv seq bound
      (growRightAllInv x C leaf hB st records hInv hLeafFV hLeafBV hLeafBVSub).2 := by
-- BEGIN PROOF
  unfold growRightAllInv
  simp only
  exact hInv

helper /-- `appendTERM1` preserves `availNext`. -/
theorem appendTERM1_availNext_eq {L : Language} {supply : TermStream L} (st : SearchState L supply)
    (y : Term L) :
    (st.appendTERM1 y).availNext = st.availNext := rfl

helper /-- `tailAVAIL0` increments `availNext` by one. -/
theorem tailAVAIL0_availNext_eq {L : Language} {supply : TermStream L} (st : SearchState L supply) :
    st.tailAVAIL0.availNext = st.availNext + 1 := rfl









helper /-- `growLeftExInv` leaves activation to its caller. -/
theorem growLeftExInv_availNext_eq {L : Language} {supply : TermStream L}
    {seq : Sequent L} {bound : Nat}
    (x : Nat) (A : FormulaN L) (leaf : Sequent L)
    (hA : FormulaN.ex x A ∈ leaf.antecedent)
    (st : SearchState L supply) (records : BranchRecords L) (hInv : SearchState.Inv seq bound st)
    (hLeafFV : LeafFVBelow supply leaf st.availNext)
    (hLeafBV : LeafBVBelow leaf bound)
    (hLeafBVSub : LeafBVSubsetSeq leaf seq) :
    (growLeftExInv x A leaf hA st records hInv hLeafFV hLeafBV hLeafBVSub).2.availNext
      = st.availNext := by
-- BEGIN PROOF
  unfold growLeftExInv
  rfl

helper /-- `growRightAllInv` leaves activation to its caller. -/
theorem growRightAllInv_availNext_eq {L : Language} {supply : TermStream L}
    {seq : Sequent L} {bound : Nat}
    (x : Nat) (C : FormulaN L) (leaf : Sequent L)
    (hB : FormulaN.all x C ∈ leaf.succedent)
    (st : SearchState L supply) (records : BranchRecords L) (hInv : SearchState.Inv seq bound st)
    (hLeafFV : LeafFVBelow supply leaf st.availNext)
    (hLeafBV : LeafBVBelow leaf bound)
    (hLeafBVSub : LeafBVSubsetSeq leaf seq) :
    (growRightAllInv x C leaf hB st records hInv hLeafFV hLeafBV hLeafBVSub).2.availNext
      = st.availNext := by
-- BEGIN PROOF
  unfold growRightAllInv
  rfl













helper /-- Definition 5.4.9 (required helper): `LeafBVSubsetSeq` lifts across
    a subformula `B` of `A` when `A ∈ leaf` and `BV(B) ⊆ BV(A)`. Used
    for the propositional-rule cases where the premise has
    subformulas of the principal formula in its context. -/
theorem LeafBVSubsetSeq_of_subformulaBV
    {L : Language} {leaf seq : Sequent L} {A B : FormulaN L}
    (hSub : LeafBVSubsetSeq leaf seq)
    (hAIn : A ∈ leaf.antecedent ++ leaf.succedent)
    (hBVSub : ∀ y, y ∈ formulaBVN B → y ∈ formulaBVN A) :
    ∀ y ∈ formulaBVN B,
      ∃ G ∈ seq.antecedent ++ seq.succedent, y ∈ formulaBVN G := by
-- BEGIN PROOF
  intro y hy
  exact hSub A hAIn y (hBVSub y hy)

helper /-- Definition 5.4.9 (required helper): `LeafFVBelow` lifts across a
    subformula `B` of `A` when `A ∈ leaf` and `FV(B) ⊆ FV(A)`. Used
    for the propositional-rule cases. -/
theorem LeafFVBelow_of_subformulaFV
    {L : Language} {supply : TermStream L} {leaf : Sequent L} {bound : Nat} {A B : FormulaN L}
    (hFV : LeafFVBelow supply leaf bound)
    (hAIn : A ∈ leaf.antecedent ++ leaf.succedent)
    (hFVSub : ∀ j, j ∈ formulaFVN B → j ∈ formulaFVN A) :
    ∀ j ∈ formulaFVN B, BeforeCursor supply bound j := fun j hj =>
  hFV A hAIn j (hFVSub j hj)





helper /-- Definition 5.4.9 (required helper): Preservation of `TreeLeafInv`
    for the propositional grow-left case. Given split witnesses, the
    premise's antecedent is `Γ ++ moreAnt ++ Δ` where
    `Γ ++ [A] ++ Δ = leaf.antecedent` and `moreAnt` is a list of
    subformulas of `A`. The premise's succedent is
    `leaf.succedent ++ moreSucc` where `moreSucc` is also subformulas
    of A. Shows the new leaf satisfies LeafFVBelow and LeafBVSubsetSeq. -/
theorem leafInv_of_propLeft {L : Language} {supply : TermStream L}
    {seq leaf : Sequent L} {bound : Nat} {A : FormulaN L}
    (hLeafFV : LeafFVBelow supply leaf bound)
    (hLeafBVSub : LeafBVSubsetSeq leaf seq)
    (hAIn : A ∈ leaf.antecedent)
    {Γ Δ : List (FormulaN L)} (hSplit : leaf.antecedent = Γ ++ [A] ++ Δ)
    {moreAnt moreSucc : List (FormulaN L)}
    (hMoreAnt : ∀ F ∈ moreAnt,
      (∀ j, j ∈ formulaFVN F → j ∈ formulaFVN A) ∧
      (∀ y, y ∈ formulaBVN F → y ∈ formulaBVN A))
    (hMoreSucc : ∀ F ∈ moreSucc,
      (∀ j, j ∈ formulaFVN F → j ∈ formulaFVN A) ∧
      (∀ y, y ∈ formulaBVN F → y ∈ formulaBVN A))
    (newPreAnt : List (FormulaN L))
    (hPreAnt : ∀ F ∈ newPreAnt, F ∈ leaf.antecedent) :
    LeafFVBelow supply
      (Sequent.mk (newPreAnt ++ moreAnt ++ Δ) (leaf.succedent ++ moreSucc)) bound ∧
    LeafBVSubsetSeq
      (Sequent.mk (newPreAnt ++ moreAnt ++ Δ) (leaf.succedent ++ moreSucc)) seq := by
-- BEGIN PROOF
  have hAInList : A ∈ leaf.antecedent ++ leaf.succedent :=
    mem_antSucc_of_mem_antecedent hAIn
  have hΔInList : ∀ F ∈ Δ, F ∈ leaf.antecedent ++ leaf.succedent := by
    intro F hF
    apply mem_antSucc_of_mem_antecedent
    rw [hSplit]
    exact List.mem_append.mpr (Or.inr hF)
  refine ⟨?_, ?_⟩
  · intro F hF j hj
    simp only [List.mem_append] at hF
    rcases hF with (hFAnt | hFSucc)
    · rcases hFAnt with (hFnew_or_more | hFΔ)
      · rcases hFnew_or_more with hFnew | hFmore
        · exact hLeafFV F (mem_antSucc_of_mem_antecedent (hPreAnt F hFnew)) j hj
        · exact hLeafFV A hAInList j ((hMoreAnt F hFmore).1 j hj)
      · exact hLeafFV F (hΔInList F hFΔ) j hj
    · rcases hFSucc with hFLeafSucc | hFmoreSucc
      · exact hLeafFV F (mem_antSucc_of_mem_succedent hFLeafSucc) j hj
      · exact hLeafFV A hAInList j ((hMoreSucc F hFmoreSucc).1 j hj)
  · intro F hF y hy
    simp only [List.mem_append] at hF
    rcases hF with (hFAnt | hFSucc)
    · rcases hFAnt with (hFnew_or_more | hFΔ)
      · rcases hFnew_or_more with hFnew | hFmore
        · exact hLeafBVSub F (mem_antSucc_of_mem_antecedent (hPreAnt F hFnew)) y hy
        · exact hLeafBVSub A hAInList y ((hMoreAnt F hFmore).2 y hy)
      · exact hLeafBVSub F (hΔInList F hFΔ) y hy
    · rcases hFSucc with hFLeafSucc | hFmoreSucc
      · exact hLeafBVSub F (mem_antSucc_of_mem_succedent hFLeafSucc) y hy
      · exact hLeafBVSub A hAInList y ((hMoreSucc F hFmoreSucc).2 y hy)

end LCS.FirstOrder.Gentzen.Search.NoFunction

end
