import LCS.Item
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.Hintikka
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics.Subformulae
import LCS.FirstOrder.Gentzen.Search.NoFunction.Initialization
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

/-- Definition 5.4.9 (required helper): Mirror of `leafInv_of_propLeft`
    for right-rule propositional cases. The new premise's succedent
    is `Δ ++ moreSucc ++ Λ`, antecedent is `moreAnt ++ leaf.antecedent`. -/
theorem leafInv_of_propRight {L : Language} {supply : TermStream L}
    {seq leaf : Sequent L} {bound : Nat} {B : FormulaN L}
    (hLeafFV : LeafFVBelow supply leaf bound)
    (hLeafBVSub : LeafBVSubsetSeq leaf seq)
    (hBIn : B ∈ leaf.succedent)
    {Δ Λ : List (FormulaN L)} (hSplit : leaf.succedent = Δ ++ [B] ++ Λ)
    {moreAnt moreSucc : List (FormulaN L)}
    (hMoreAnt : ∀ F ∈ moreAnt,
      (∀ j, j ∈ formulaFVN F → j ∈ formulaFVN B) ∧
      (∀ y, y ∈ formulaBVN F → y ∈ formulaBVN B))
    (hMoreSucc : ∀ F ∈ moreSucc,
      (∀ j, j ∈ formulaFVN F → j ∈ formulaFVN B) ∧
      (∀ y, y ∈ formulaBVN F → y ∈ formulaBVN B))
    (newPreSucc : List (FormulaN L))
    (hPreSucc : ∀ F ∈ newPreSucc, F ∈ leaf.succedent) :
    LeafFVBelow supply
      (Sequent.mk (moreAnt ++ leaf.antecedent) (Δ ++ newPreSucc ++ Λ)) bound ∧
    LeafBVSubsetSeq
      (Sequent.mk (moreAnt ++ leaf.antecedent) (Δ ++ newPreSucc ++ Λ)) seq := by
-- BEGIN PROOF
  have hBInList : B ∈ leaf.antecedent ++ leaf.succedent :=
    mem_antSucc_of_mem_succedent hBIn
  have hΔInList : ∀ F ∈ Δ, F ∈ leaf.antecedent ++ leaf.succedent := by
    intro F hF
    apply mem_antSucc_of_mem_succedent
    rw [hSplit]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hF)))
  have hΛInList : ∀ F ∈ Λ, F ∈ leaf.antecedent ++ leaf.succedent := by
    intro F hF
    apply mem_antSucc_of_mem_succedent
    rw [hSplit]
    exact List.mem_append.mpr (Or.inr hF)
  refine ⟨?_, ?_⟩
  · intro F hF j hj
    simp only [List.mem_append] at hF
    rcases hF with (hFAnt | hFSucc)
    · rcases hFAnt with hFmore | hFleaf
      · exact hLeafFV B hBInList j ((hMoreAnt F hFmore).1 j hj)
      · exact hLeafFV F (mem_antSucc_of_mem_antecedent hFleaf) j hj
    · rcases hFSucc with (hFΔ_or_new | hFΛ)
      · rcases hFΔ_or_new with hFΔ | hFnew
        · exact hLeafFV F (hΔInList F hFΔ) j hj
        · exact hLeafFV F (mem_antSucc_of_mem_succedent (hPreSucc F hFnew)) j hj
      · exact hLeafFV F (hΛInList F hFΛ) j hj
  · intro F hF y hy
    simp only [List.mem_append] at hF
    rcases hF with (hFAnt | hFSucc)
    · rcases hFAnt with hFmore | hFleaf
      · exact hLeafBVSub B hBInList y ((hMoreAnt F hFmore).2 y hy)
      · exact hLeafBVSub F (mem_antSucc_of_mem_antecedent hFleaf) y hy
    · rcases hFSucc with (hFΔ_or_new | hFΛ)
      · rcases hFΔ_or_new with hFΔ | hFnew
        · exact hLeafBVSub F (hΔInList F hFΔ) y hy
        · exact hLeafBVSub F (mem_antSucc_of_mem_succedent (hPreSucc F hFnew)) y hy
      · exact hLeafBVSub F (hΛInList F hFΛ) y hy

/-- Definition 5.4.9 (companion, preservation): Applying a rule via
    `growLeftAtLeaf` preserves the tree-level leaf invariants at the
    resulting subtree.

    Case analysis over the 8 branches of `growLeftAtLeaf`:
    - No-op (`A ∉ leaf.antecedent`, atomic A): returns `(leaf, st)`,
      invariants trivially preserved.
    - Propositional (`conj/disj/impl/neg`): new premise leaves have
      subformulas of A in their context. Subformula relation preserves
      BV-subset; propositional connectives don't add FVs, so
      `LeafFVBelow` preserved.
    - `all x B`: new premise has `formulaSubstN B t x` for each
      `t ∈ ts ⊆ tTERM0 st`. `formulaSubstN` preserves BV
      (`formulaBVN_formulaSubstN_subset`), and each `t`'s FV is ≤
      `st.availNext` (by `Inv.terms_allowed` + `terms_below_avail`),
      so FV of substituted formula is bounded by `st.availNext`
      (unchanged in the ∀:left case).
    - `ex x B` (eigenvariable): new premise has `formulaSubstN B (var y) x`
      where `y = st.availNext`. FV includes `y < availNext + 1 =
      new availNext`. BV preserved by `formulaSubstN`. -/
theorem TreeLeafInv_grow_at_leaf {L : Language} {supply : TermStream L} (hNoEq : L.hasEquality = false)
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq)
    (A : FormulaN L) (leaf : Sequent L)
    (st : SearchState L supply) (records : BranchRecords L) (hInv : SearchState.Inv seq bound st)
    (hLeafFV : LeafFVBelow supply leaf st.availNext)
    (hLeafBV : LeafBVBelow leaf bound)
    (hLeafBVSub : LeafBVSubsetSeq leaf seq) :
    TreeLeafInv supply
      (growLeftAtLeaf hNoEq hNoFunc hCNFB A leaf st records hInv hLeafFV hLeafBV hLeafBVSub).1
      seq
      (growLeftAtLeaf hNoEq hNoFunc hCNFB A leaf st records hInv hLeafFV hLeafBV hLeafBVSub).2.availNext := by
-- BEGIN PROOF
  classical
  unfold growLeftAtLeaf
  split
  next hA =>
    split
    next B C hAcase =>
      -- conj case: premise has antecedent = Γ ++ [B, C] ++ Δ
      simp only [growLeftOneProp, TreeLeafInv, SearchTree.toDeductionTree]
      intro l hl
      simp only [leaves_cast] at hl
      simp only [SearchTree.toDeductionTree, GDeductionTreeExt.leaves_onePremise,
                 GDeductionTreeExt.leaves_leaf,
                 List.mem_singleton] at hl
      subst hl
      have hSplit := (splitListAt leaf.antecedent (FormulaN.conj B C) hAcase).property
      have hAInList : FormulaN.conj B C ∈ leaf.antecedent ++ leaf.succedent :=
        mem_antSucc_of_mem_antecedent hAcase
      constructor
      · intro F hF j hj
        simp only [List.mem_append, List.mem_cons, List.mem_singleton,
                   List.not_mem_nil, or_false] at hF
        rcases hF with (hFant | hFsucc)
        · rcases hFant with (hFant1 | hFΔ)
          · rcases hFant1 with hFΓ | hFB | hFC
            · have hFleaf : F ∈ leaf.antecedent := by
                rw [hSplit]
                exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΓ)))
              exact hLeafFV F (mem_antSucc_of_mem_antecedent hFleaf) j hj
            · -- hFB : F = B
              rw [hFB] at hj
              exact hLeafFV (FormulaN.conj B C) hAInList j (Or.inl hj)
            · -- hFC : F = C
              rw [hFC] at hj
              exact hLeafFV (FormulaN.conj B C) hAInList j (Or.inr hj)
          · have hFleaf : F ∈ leaf.antecedent := by
              rw [hSplit]
              exact List.mem_append.mpr (Or.inr hFΔ)
            exact hLeafFV F (mem_antSucc_of_mem_antecedent hFleaf) j hj
        · exact hLeafFV F (mem_antSucc_of_mem_succedent hFsucc) j hj
      · intro F hF y hy
        simp only [List.mem_append, List.mem_cons, List.mem_singleton,
                   List.not_mem_nil, or_false] at hF
        rcases hF with (hFant | hFsucc)
        · rcases hFant with (hFant1 | hFΔ)
          · rcases hFant1 with hFΓ | hFB | hFC
            · have hFleaf : F ∈ leaf.antecedent := by
                rw [hSplit]
                exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΓ)))
              exact hLeafBVSub F (mem_antSucc_of_mem_antecedent hFleaf) y hy
            · rw [hFB] at hy
              exact hLeafBVSub (FormulaN.conj B C) hAInList y (Or.inl hy)
            · rw [hFC] at hy
              exact hLeafBVSub (FormulaN.conj B C) hAInList y (Or.inr hy)
          · have hFleaf : F ∈ leaf.antecedent := by
              rw [hSplit]
              exact List.mem_append.mpr (Or.inr hFΔ)
            exact hLeafBVSub F (mem_antSucc_of_mem_antecedent hFleaf) y hy
        · exact hLeafBVSub F (mem_antSucc_of_mem_succedent hFsucc) y hy
    next B C hAcase =>
      -- disj case: two premises Γ++[B]++Δ and Γ++[C]++Δ
      simp only [growLeftOneProp, TreeLeafInv, SearchTree.toDeductionTree]
      intro l hl
      simp only [leaves_cast] at hl
      simp only [SearchTree.toDeductionTree, GDeductionTreeExt.leaves_twoPremise,
                 GDeductionTreeExt.leaves_leaf,
                 List.mem_append, List.mem_singleton] at hl
      have hSplit := (splitListAt leaf.antecedent (FormulaN.disj B C) hAcase).property
      have hAInList : FormulaN.disj B C ∈ leaf.antecedent ++ leaf.succedent :=
        mem_antSucc_of_mem_antecedent hAcase
      rcases hl with hlL | hlR
      · -- premL
        subst hlL
        constructor
        · intro F hF j hj
          simp only [List.mem_append, List.mem_singleton] at hF
          rcases hF with (hFant | hFsucc)
          · rcases hFant with (hFant1 | hFΔ)
            · rcases hFant1 with hFΓ | hFeqB
              · have hFleaf : F ∈ leaf.antecedent := by
                  rw [hSplit]
                  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΓ)))
                exact hLeafFV F (mem_antSucc_of_mem_antecedent hFleaf) j hj
              · rw [hFeqB] at hj
                exact hLeafFV (FormulaN.disj B C) hAInList j (Or.inl hj)
            · have hFleaf : F ∈ leaf.antecedent := by
                rw [hSplit]
                exact List.mem_append.mpr (Or.inr hFΔ)
              exact hLeafFV F (mem_antSucc_of_mem_antecedent hFleaf) j hj
          · exact hLeafFV F (mem_antSucc_of_mem_succedent hFsucc) j hj
        · intro F hF y hy
          simp only [List.mem_append, List.mem_singleton] at hF
          rcases hF with (hFant | hFsucc)
          · rcases hFant with (hFant1 | hFΔ)
            · rcases hFant1 with hFΓ | hFeqB
              · have hFleaf : F ∈ leaf.antecedent := by
                  rw [hSplit]
                  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΓ)))
                exact hLeafBVSub F (mem_antSucc_of_mem_antecedent hFleaf) y hy
              · rw [hFeqB] at hy
                exact hLeafBVSub (FormulaN.disj B C) hAInList y (Or.inl hy)
            · have hFleaf : F ∈ leaf.antecedent := by
                rw [hSplit]
                exact List.mem_append.mpr (Or.inr hFΔ)
              exact hLeafBVSub F (mem_antSucc_of_mem_antecedent hFleaf) y hy
          · exact hLeafBVSub F (mem_antSucc_of_mem_succedent hFsucc) y hy
      · -- premR
        subst hlR
        constructor
        · intro F hF j hj
          simp only [List.mem_append, List.mem_singleton] at hF
          rcases hF with (hFant | hFsucc)
          · rcases hFant with (hFant1 | hFΔ)
            · rcases hFant1 with hFΓ | hFeqC
              · have hFleaf : F ∈ leaf.antecedent := by
                  rw [hSplit]
                  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΓ)))
                exact hLeafFV F (mem_antSucc_of_mem_antecedent hFleaf) j hj
              · rw [hFeqC] at hj
                exact hLeafFV (FormulaN.disj B C) hAInList j (Or.inr hj)
            · have hFleaf : F ∈ leaf.antecedent := by
                rw [hSplit]
                exact List.mem_append.mpr (Or.inr hFΔ)
              exact hLeafFV F (mem_antSucc_of_mem_antecedent hFleaf) j hj
          · exact hLeafFV F (mem_antSucc_of_mem_succedent hFsucc) j hj
        · intro F hF y hy
          simp only [List.mem_append, List.mem_singleton] at hF
          rcases hF with (hFant | hFsucc)
          · rcases hFant with (hFant1 | hFΔ)
            · rcases hFant1 with hFΓ | hFeqC
              · have hFleaf : F ∈ leaf.antecedent := by
                  rw [hSplit]
                  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΓ)))
                exact hLeafBVSub F (mem_antSucc_of_mem_antecedent hFleaf) y hy
              · rw [hFeqC] at hy
                exact hLeafBVSub (FormulaN.disj B C) hAInList y (Or.inr hy)
            · have hFleaf : F ∈ leaf.antecedent := by
                rw [hSplit]
                exact List.mem_append.mpr (Or.inr hFΔ)
              exact hLeafBVSub F (mem_antSucc_of_mem_antecedent hFleaf) y hy
          · exact hLeafBVSub F (mem_antSucc_of_mem_succedent hFsucc) y hy
    next B C hAcase =>
      -- impl case: premL (Γ++Δ, [B]++leaf.succedent), premR ([C]++Γ++Δ, leaf.succedent)
      simp only [growLeftOneProp, TreeLeafInv, SearchTree.toDeductionTree]
      intro l hl
      simp only [leaves_cast] at hl
      simp only [SearchTree.toDeductionTree, GDeductionTreeExt.leaves_twoPremise,
                 GDeductionTreeExt.leaves_leaf,
                 List.mem_append, List.mem_singleton] at hl
      have hSplit := (splitListAt leaf.antecedent (FormulaN.impl B C) hAcase).property
      have hAInList : FormulaN.impl B C ∈ leaf.antecedent ++ leaf.succedent :=
        mem_antSucc_of_mem_antecedent hAcase
      rcases hl with hlL | hlR
      · -- premL: antecedent = Γ++Δ, succedent = [B]++leaf.succedent
        subst hlL
        constructor
        · intro F hF j hj
          simp only [List.mem_append, List.mem_singleton] at hF
          rcases hF with (hFant | hFsucc)
          · have hFleaf : F ∈ leaf.antecedent := by
              rw [hSplit]
              rcases hFant with hFΓ | hFΔ
              · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΓ)))
              · exact List.mem_append.mpr (Or.inr hFΔ)
            exact hLeafFV F (mem_antSucc_of_mem_antecedent hFleaf) j hj
          · rcases hFsucc with hFeqB | hFLeafSucc
            · rw [hFeqB] at hj
              exact hLeafFV (FormulaN.impl B C) hAInList j (Or.inl hj)
            · exact hLeafFV F (mem_antSucc_of_mem_succedent hFLeafSucc) j hj
        · intro F hF y hy
          simp only [List.mem_append, List.mem_singleton] at hF
          rcases hF with (hFant | hFsucc)
          · have hFleaf : F ∈ leaf.antecedent := by
              rw [hSplit]
              rcases hFant with hFΓ | hFΔ
              · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΓ)))
              · exact List.mem_append.mpr (Or.inr hFΔ)
            exact hLeafBVSub F (mem_antSucc_of_mem_antecedent hFleaf) y hy
          · rcases hFsucc with hFeqB | hFLeafSucc
            · rw [hFeqB] at hy
              exact hLeafBVSub (FormulaN.impl B C) hAInList y (Or.inl hy)
            · exact hLeafBVSub F (mem_antSucc_of_mem_succedent hFLeafSucc) y hy
      · -- premR: antecedent = [C]++Γ++Δ, succedent = leaf.succedent
        subst hlR
        constructor
        · intro F hF j hj
          simp only [List.mem_append, List.mem_singleton] at hF
          rcases hF with (hFant | hFsucc)
          · rcases hFant with (hFant1 | hFΔ)
            · rcases hFant1 with hFc | hFΓ
              · rw [hFc] at hj
                exact hLeafFV (FormulaN.impl B C) hAInList j (Or.inr hj)
              · have hFleaf : F ∈ leaf.antecedent := by
                  rw [hSplit]
                  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΓ)))
                exact hLeafFV F (mem_antSucc_of_mem_antecedent hFleaf) j hj
            · have hFleaf : F ∈ leaf.antecedent := by
                rw [hSplit]
                exact List.mem_append.mpr (Or.inr hFΔ)
              exact hLeafFV F (mem_antSucc_of_mem_antecedent hFleaf) j hj
          · exact hLeafFV F (mem_antSucc_of_mem_succedent hFsucc) j hj
        · intro F hF y hy
          simp only [List.mem_append, List.mem_singleton] at hF
          rcases hF with (hFant | hFsucc)
          · rcases hFant with (hFant1 | hFΔ)
            · rcases hFant1 with hFc | hFΓ
              · rw [hFc] at hy
                exact hLeafBVSub (FormulaN.impl B C) hAInList y (Or.inr hy)
              · have hFleaf : F ∈ leaf.antecedent := by
                  rw [hSplit]
                  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΓ)))
                exact hLeafBVSub F (mem_antSucc_of_mem_antecedent hFleaf) y hy
            · have hFleaf : F ∈ leaf.antecedent := by
                rw [hSplit]
                exact List.mem_append.mpr (Or.inr hFΔ)
              exact hLeafBVSub F (mem_antSucc_of_mem_antecedent hFleaf) y hy
          · exact hLeafBVSub F (mem_antSucc_of_mem_succedent hFsucc) y hy
    next B hAcase =>
      -- neg case: premise = (Γ++Δ, [B]++leaf.succedent)
      simp only [growLeftOneProp, TreeLeafInv, SearchTree.toDeductionTree]
      intro l hl
      simp only [leaves_cast] at hl
      simp only [SearchTree.toDeductionTree, GDeductionTreeExt.leaves_onePremise,
                 GDeductionTreeExt.leaves_leaf,
                 List.mem_singleton] at hl
      subst hl
      have hSplit := (splitListAt leaf.antecedent (FormulaN.neg B) hAcase).property
      have hAInList : FormulaN.neg B ∈ leaf.antecedent ++ leaf.succedent :=
        mem_antSucc_of_mem_antecedent hAcase
      constructor
      · intro F hF j hj
        simp only [List.mem_append, List.mem_singleton] at hF
        rcases hF with (hFant | hFsucc)
        · have hFleaf : F ∈ leaf.antecedent := by
            rw [hSplit]
            rcases hFant with hFΓ | hFΔ
            · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΓ)))
            · exact List.mem_append.mpr (Or.inr hFΔ)
          exact hLeafFV F (mem_antSucc_of_mem_antecedent hFleaf) j hj
        · rcases hFsucc with hFeqB | hFLeafSucc
          · rw [hFeqB] at hj
            exact hLeafFV (FormulaN.neg B) hAInList j hj
          · exact hLeafFV F (mem_antSucc_of_mem_succedent hFLeafSucc) j hj
      · intro F hF y hy
        simp only [List.mem_append, List.mem_singleton] at hF
        rcases hF with (hFant | hFsucc)
        · have hFleaf : F ∈ leaf.antecedent := by
            rw [hSplit]
            rcases hFant with hFΓ | hFΔ
            · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΓ)))
            · exact List.mem_append.mpr (Or.inr hFΔ)
          exact hLeafBVSub F (mem_antSucc_of_mem_antecedent hFleaf) y hy
        · rcases hFsucc with hFeqB | hFLeafSucc
          · rw [hFeqB] at hy
            exact hLeafBVSub (FormulaN.neg B) hAInList y hy
          · exact hLeafBVSub F (mem_antSucc_of_mem_succedent hFLeafSucc) y hy
    next =>
      -- predN case: no-op
      simp only [TreeLeafInv, SearchTree.toDeductionTree, GDeductionTreeExt.leaves_leaf]
      intro l hl
      simp only [List.mem_singleton] at hl
      subst hl
      exact ⟨hLeafFV, hLeafBVSub⟩
    next =>
      -- eq_ case: no-op
      simp only [TreeLeafInv, SearchTree.toDeductionTree, GDeductionTreeExt.leaves_leaf]
      intro l hl
      simp only [List.mem_singleton] at hl
      subst hl
      exact ⟨hLeafFV, hLeafBVSub⟩
    next x B hAcase =>
      -- all case: growLeftAllInv
      simp only [TreeLeafInv, SearchTree.toDeductionTree]
      unfold growLeftAllInv
      simp only
      classical
      by_cases hEmpty :
        ((st.tTERM0.mapIdx (fun k t => (t, k))).filter
          (fun p => ¬ SearchState.isUsed records p.2 (FormulaN.all x B))).map Prod.fst = []
      · simp only [hEmpty, dif_pos, SearchTree.toDeductionTree, GDeductionTreeExt.leaves_leaf]
        intro l hl
        simp only [List.mem_singleton] at hl
        subst hl
        exact ⟨hLeafFV, hLeafBVSub⟩
      · rw [dif_neg hEmpty]
        intro l hl
        simp only [leaves_cast] at hl
        simp only [SearchTree.toDeductionTree, GDeductionTreeExt.leaves_onePremise,
                   GDeductionTreeExt.leaves_leaf,
                   List.mem_singleton] at hl
        subst hl
        have hSplit := (splitListAt leaf.antecedent (FormulaN.all x B) hAcase).property
        have hAllInList : FormulaN.all x B ∈ leaf.antecedent ++ leaf.succedent :=
          mem_antSucc_of_mem_antecedent hAcase
        constructor
        · -- LeafFVBelow supply
          intro F hF j hj
          simp only [List.mem_append, List.mem_singleton] at hF
          rcases hF with (hFant | hFsucc)
          · rcases hFant with (hFant1 | hFΔ)
            · rcases hFant1 with (hFΓ_or_ts | hFAllEq)
              · rcases hFΓ_or_ts with hFΓ | hFts
                · -- F ∈ Γ
                  have hFleaf : F ∈ leaf.antecedent := by
                    rw [hSplit]
                    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΓ)))
                  exact hLeafFV F (mem_antSucc_of_mem_antecedent hFleaf) j hj
                · -- F ∈ ts.map (fun t => formulaSubstN B t x)
                  rw [List.mem_map] at hFts
                  obtain ⟨t, htTS, htF⟩ := hFts
                  subst htF
                  have hjCases := formulaFVN_formulaSubstN B t x j hj
                  rcases hjCases with ⟨hjB, hjne⟩ | hjT
                  · have hjAll : j ∈ formulaFVN (FormulaN.all x B) :=
                      ⟨hjB, fun heq => hjne heq⟩
                    exact hLeafFV (FormulaN.all x B) hAllInList j hjAll
                  · have htTTERM0 : t ∈ st.tTERM0 := by
                      unfold SearchState.tTERM0
                      rw [List.mem_map] at htTS
                      obtain ⟨p, hpFilt, hpt⟩ := htTS
                      have hpIdx : p ∈ (st.TERM0.mapIdx (fun k t => (t, k))) :=
                        (List.mem_filter.mp hpFilt).1
                      rw [List.mem_mapIdx] at hpIdx
                      obtain ⟨i, hi, hpEq⟩ := hpIdx
                      have h1 : (st.TERM0[i], i) = p := hpEq
                      have h2 : p.1 = st.TERM0[i] := congrArg Prod.fst h1.symm
                      rw [← hpt, h2]
                      exact List.getElem_mem hi
                    exact termFV_of_tTERM0_lt_availNext hNoFunc hInv htTTERM0 j hjT
              · -- hFAllEq : F = FormulaN.all x B
                rw [hFAllEq] at hj
                exact hLeafFV (FormulaN.all x B) hAllInList j hj
            · have hFleaf : F ∈ leaf.antecedent := by
                rw [hSplit]
                exact List.mem_append.mpr (Or.inr hFΔ)
              exact hLeafFV F (mem_antSucc_of_mem_antecedent hFleaf) j hj
          · exact hLeafFV F (mem_antSucc_of_mem_succedent hFsucc) j hj
        · -- LeafBVSubsetSeq
          intro F hF y hy
          simp only [List.mem_append, List.mem_singleton] at hF
          rcases hF with (hFant | hFsucc)
          · rcases hFant with (hFant1 | hFΔ)
            · rcases hFant1 with (hFΓ_or_ts | hFAllEq)
              · rcases hFΓ_or_ts with hFΓ | hFts
                · have hFleaf : F ∈ leaf.antecedent := by
                    rw [hSplit]
                    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΓ)))
                  exact hLeafBVSub F (mem_antSucc_of_mem_antecedent hFleaf) y hy
                · rw [List.mem_map] at hFts
                  obtain ⟨t, _, htF⟩ := hFts
                  rw [← htF] at hy
                  have hyB : y ∈ formulaBVN B :=
                    @formulaBVN_formulaSubstN_subset _ B t x y hy
                  have hyAll : y ∈ formulaBVN (FormulaN.all x B) := Or.inl hyB
                  exact hLeafBVSub (FormulaN.all x B) hAllInList y hyAll
              · rw [hFAllEq] at hy
                exact hLeafBVSub (FormulaN.all x B) hAllInList y hy
            · have hFleaf : F ∈ leaf.antecedent := by
                rw [hSplit]
                exact List.mem_append.mpr (Or.inr hFΔ)
              exact hLeafBVSub F (mem_antSucc_of_mem_antecedent hFleaf) y hy
          · exact hLeafBVSub F (mem_antSucc_of_mem_succedent hFsucc) y hy
    next x B hAcase =>
      -- ex case: growLeftExInv
      simp only [TreeLeafInv, SearchTree.toDeductionTree]
      unfold growLeftExInv
      simp only
      intro l hl
      simp only [leaves_cast] at hl
      simp only [SearchTree.toDeductionTree, GDeductionTreeExt.leaves_onePremise,
                 GDeductionTreeExt.leaves_leaf,
                 List.mem_singleton] at hl
      subst hl
      have hSplit := (splitListAt leaf.antecedent (FormulaN.ex x B) hAcase).property
      have hExInList : FormulaN.ex x B ∈ leaf.antecedent ++ leaf.succedent :=
        mem_antSucc_of_mem_antecedent hAcase
      -- new availNext = st.availNext + 1
      constructor
      · intro F hF j hj
        simp only [List.mem_append, List.mem_singleton] at hF
        rcases hF with (hFant | hFsucc)
        · rcases hFant with (hFant1 | hFΔ)
          · rcases hFant1 with hFΓ | hFeqSubst
            · have hFleaf : F ∈ leaf.antecedent := by
                rw [hSplit]
                exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΓ)))
              have h := hLeafFV F (mem_antSucc_of_mem_antecedent hFleaf) j hj
              exact BeforeCursor.mono h (Nat.le_succ _)
            · rw [hFeqSubst] at hj
              have hjCases := formulaFVN_formulaSubstN B (Term.var (supply.varAt st.availNext (hInv.available_vars st.availNext))) x j hj
              rcases hjCases with ⟨hjB, hjne⟩ | hjT
              · have hjEx : j ∈ formulaFVN (FormulaN.ex x B) :=
                  ⟨hjB, fun heq => hjne heq⟩
                have h := hLeafFV (FormulaN.ex x B) hExInList j hjEx
                exact BeforeCursor.mono h (Nat.le_succ _)
              · have hj_eq : j = supply.varAt st.availNext (hInv.available_vars st.availNext) := hjT
                subst hj_eq
                exact supply.varAt_beforeSucc st.availNext (hInv.available_vars st.availNext)
          · have hFleaf : F ∈ leaf.antecedent := by
              rw [hSplit]
              exact List.mem_append.mpr (Or.inr hFΔ)
            have h := hLeafFV F (mem_antSucc_of_mem_antecedent hFleaf) j hj
            exact BeforeCursor.mono h (Nat.le_succ _)
        · have h := hLeafFV F (mem_antSucc_of_mem_succedent hFsucc) j hj
          exact BeforeCursor.mono h (Nat.le_succ _)
      · intro F hF y hy
        simp only [List.mem_append, List.mem_singleton] at hF
        rcases hF with (hFant | hFsucc)
        · rcases hFant with (hFant1 | hFΔ)
          · rcases hFant1 with hFΓ | hFeqSubst
            · have hFleaf : F ∈ leaf.antecedent := by
                rw [hSplit]
                exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΓ)))
              exact hLeafBVSub F (mem_antSucc_of_mem_antecedent hFleaf) y hy
            · rw [hFeqSubst] at hy
              have hyB : y ∈ formulaBVN B :=
                @formulaBVN_formulaSubstN_subset _ B (Term.var (supply.varAt st.availNext (hInv.available_vars st.availNext))) x y hy
              have hyEx : y ∈ formulaBVN (FormulaN.ex x B) := Or.inl hyB
              exact hLeafBVSub (FormulaN.ex x B) hExInList y hyEx
          · have hFleaf : F ∈ leaf.antecedent := by
              rw [hSplit]
              exact List.mem_append.mpr (Or.inr hFΔ)
            exact hLeafBVSub F (mem_antSucc_of_mem_antecedent hFleaf) y hy
        · exact hLeafBVSub F (mem_antSucc_of_mem_succedent hFsucc) y hy
  next hA =>
    -- A ∉ leaf.antecedent: no-op, result is (leaf, st)
    simp only [TreeLeafInv, SearchTree.toDeductionTree, GDeductionTreeExt.leaves_leaf]
    intro l hl
    simp only [List.mem_singleton] at hl
    subst hl
    exact ⟨hLeafFV, hLeafBVSub⟩

/-- Definition 5.4.9 (companion, preservation): Mirror of
    `TreeLeafInv_grow_at_leaf` for the right-side rules: applying
    `growRightAtLeaf` preserves `TreeLeafInv`. -/
theorem TreeLeafInv_grow_right_at_leaf {L : Language} {supply : TermStream L} (hNoEq : L.hasEquality = false)
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq)
    (B : FormulaN L) (leaf : Sequent L)
    (st : SearchState L supply) (records : BranchRecords L) (hInv : SearchState.Inv seq bound st)
    (hLeafFV : LeafFVBelow supply leaf st.availNext)
    (hLeafBV : LeafBVBelow leaf bound)
    (hLeafBVSub : LeafBVSubsetSeq leaf seq) :
    TreeLeafInv supply
      (growRightAtLeaf hNoEq hNoFunc hCNFB B leaf st records hInv hLeafFV hLeafBV hLeafBVSub).1
      seq
      (growRightAtLeaf hNoEq hNoFunc hCNFB B leaf st records hInv hLeafFV hLeafBV hLeafBVSub).2.availNext := by
-- BEGIN PROOF
  classical
  unfold growRightAtLeaf
  split
  next hB =>
    split
    next X Y hBcase =>
      -- conj case: two premises Δ++[X]++Λ and Δ++[Y]++Λ, antecedent = leaf.antecedent
      simp only [growRightOneProp, TreeLeafInv, SearchTree.toDeductionTree]
      intro l hl
      simp only [leaves_cast] at hl
      simp only [SearchTree.toDeductionTree, GDeductionTreeExt.leaves_twoPremise,
                 GDeductionTreeExt.leaves_leaf,
                 List.mem_append, List.mem_singleton] at hl
      have hSplit := (splitListAt leaf.succedent (FormulaN.conj X Y) hBcase).property
      have hBInList : FormulaN.conj X Y ∈ leaf.antecedent ++ leaf.succedent :=
        mem_antSucc_of_mem_succedent hBcase
      rcases hl with hlL | hlR
      · -- premL: succedent = Δ++[X]++Λ, antecedent = leaf.antecedent
        subst hlL
        constructor
        · intro F hF j hj
          simp only [List.mem_append, List.mem_singleton] at hF
          rcases hF with (hFant | hFsucc)
          · exact hLeafFV F (mem_antSucc_of_mem_antecedent hFant) j hj
          · rcases hFsucc with (hFsucc1 | hFΛ)
            · rcases hFsucc1 with hFΔ | hFeqX
              · have hFleaf : F ∈ leaf.succedent := by
                  rw [hSplit]
                  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΔ)))
                exact hLeafFV F (mem_antSucc_of_mem_succedent hFleaf) j hj
              · rw [hFeqX] at hj
                exact hLeafFV (FormulaN.conj X Y) hBInList j (Or.inl hj)
            · have hFleaf : F ∈ leaf.succedent := by
                rw [hSplit]
                exact List.mem_append.mpr (Or.inr hFΛ)
              exact hLeafFV F (mem_antSucc_of_mem_succedent hFleaf) j hj
        · intro F hF y hy
          simp only [List.mem_append, List.mem_singleton] at hF
          rcases hF with (hFant | hFsucc)
          · exact hLeafBVSub F (mem_antSucc_of_mem_antecedent hFant) y hy
          · rcases hFsucc with (hFsucc1 | hFΛ)
            · rcases hFsucc1 with hFΔ | hFeqX
              · have hFleaf : F ∈ leaf.succedent := by
                  rw [hSplit]
                  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΔ)))
                exact hLeafBVSub F (mem_antSucc_of_mem_succedent hFleaf) y hy
              · rw [hFeqX] at hy
                exact hLeafBVSub (FormulaN.conj X Y) hBInList y (Or.inl hy)
            · have hFleaf : F ∈ leaf.succedent := by
                rw [hSplit]
                exact List.mem_append.mpr (Or.inr hFΛ)
              exact hLeafBVSub F (mem_antSucc_of_mem_succedent hFleaf) y hy
      · -- premR: succedent = Δ++[Y]++Λ
        subst hlR
        constructor
        · intro F hF j hj
          simp only [List.mem_append, List.mem_singleton] at hF
          rcases hF with (hFant | hFsucc)
          · exact hLeafFV F (mem_antSucc_of_mem_antecedent hFant) j hj
          · rcases hFsucc with (hFsucc1 | hFΛ)
            · rcases hFsucc1 with hFΔ | hFeqY
              · have hFleaf : F ∈ leaf.succedent := by
                  rw [hSplit]
                  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΔ)))
                exact hLeafFV F (mem_antSucc_of_mem_succedent hFleaf) j hj
              · rw [hFeqY] at hj
                exact hLeafFV (FormulaN.conj X Y) hBInList j (Or.inr hj)
            · have hFleaf : F ∈ leaf.succedent := by
                rw [hSplit]
                exact List.mem_append.mpr (Or.inr hFΛ)
              exact hLeafFV F (mem_antSucc_of_mem_succedent hFleaf) j hj
        · intro F hF y hy
          simp only [List.mem_append, List.mem_singleton] at hF
          rcases hF with (hFant | hFsucc)
          · exact hLeafBVSub F (mem_antSucc_of_mem_antecedent hFant) y hy
          · rcases hFsucc with (hFsucc1 | hFΛ)
            · rcases hFsucc1 with hFΔ | hFeqY
              · have hFleaf : F ∈ leaf.succedent := by
                  rw [hSplit]
                  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΔ)))
                exact hLeafBVSub F (mem_antSucc_of_mem_succedent hFleaf) y hy
              · rw [hFeqY] at hy
                exact hLeafBVSub (FormulaN.conj X Y) hBInList y (Or.inr hy)
            · have hFleaf : F ∈ leaf.succedent := by
                rw [hSplit]
                exact List.mem_append.mpr (Or.inr hFΛ)
              exact hLeafBVSub F (mem_antSucc_of_mem_succedent hFleaf) y hy
    next X Y hBcase =>
      -- disj case: one premise succedent = Δ++[X, Y]++Λ
      simp only [growRightOneProp, TreeLeafInv, SearchTree.toDeductionTree]
      intro l hl
      simp only [leaves_cast] at hl
      simp only [SearchTree.toDeductionTree, GDeductionTreeExt.leaves_onePremise,
                 GDeductionTreeExt.leaves_leaf,
                 List.mem_singleton] at hl
      subst hl
      have hSplit := (splitListAt leaf.succedent (FormulaN.disj X Y) hBcase).property
      have hBInList : FormulaN.disj X Y ∈ leaf.antecedent ++ leaf.succedent :=
        mem_antSucc_of_mem_succedent hBcase
      constructor
      · intro F hF j hj
        simp only [List.mem_append, List.mem_cons, List.mem_singleton,
                   List.not_mem_nil, or_false] at hF
        rcases hF with (hFant | hFsucc)
        · exact hLeafFV F (mem_antSucc_of_mem_antecedent hFant) j hj
        · rcases hFsucc with (hFsucc1 | hFΛ)
          · rcases hFsucc1 with hFΔ | hFeqX | hFeqY
            · have hFleaf : F ∈ leaf.succedent := by
                rw [hSplit]
                exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΔ)))
              exact hLeafFV F (mem_antSucc_of_mem_succedent hFleaf) j hj
            · rw [hFeqX] at hj
              exact hLeafFV (FormulaN.disj X Y) hBInList j (Or.inl hj)
            · rw [hFeqY] at hj
              exact hLeafFV (FormulaN.disj X Y) hBInList j (Or.inr hj)
          · have hFleaf : F ∈ leaf.succedent := by
              rw [hSplit]
              exact List.mem_append.mpr (Or.inr hFΛ)
            exact hLeafFV F (mem_antSucc_of_mem_succedent hFleaf) j hj
      · intro F hF y hy
        simp only [List.mem_append, List.mem_cons, List.mem_singleton,
                   List.not_mem_nil, or_false] at hF
        rcases hF with (hFant | hFsucc)
        · exact hLeafBVSub F (mem_antSucc_of_mem_antecedent hFant) y hy
        · rcases hFsucc with (hFsucc1 | hFΛ)
          · rcases hFsucc1 with hFΔ | hFeqX | hFeqY
            · have hFleaf : F ∈ leaf.succedent := by
                rw [hSplit]
                exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΔ)))
              exact hLeafBVSub F (mem_antSucc_of_mem_succedent hFleaf) y hy
            · rw [hFeqX] at hy
              exact hLeafBVSub (FormulaN.disj X Y) hBInList y (Or.inl hy)
            · rw [hFeqY] at hy
              exact hLeafBVSub (FormulaN.disj X Y) hBInList y (Or.inr hy)
          · have hFleaf : F ∈ leaf.succedent := by
              rw [hSplit]
              exact List.mem_append.mpr (Or.inr hFΛ)
            exact hLeafBVSub F (mem_antSucc_of_mem_succedent hFleaf) y hy
    next X Y hBcase =>
      -- impl case: premise antecedent = [X]++leaf.antecedent, succedent = [Y]++Δ++Λ
      simp only [growRightOneProp, TreeLeafInv, SearchTree.toDeductionTree]
      intro l hl
      simp only [leaves_cast] at hl
      simp only [SearchTree.toDeductionTree, GDeductionTreeExt.leaves_onePremise,
                 GDeductionTreeExt.leaves_leaf,
                 List.mem_singleton] at hl
      subst hl
      have hSplit := (splitListAt leaf.succedent (FormulaN.impl X Y) hBcase).property
      have hBInList : FormulaN.impl X Y ∈ leaf.antecedent ++ leaf.succedent :=
        mem_antSucc_of_mem_succedent hBcase
      constructor
      · intro F hF j hj
        simp only [List.mem_append, List.mem_singleton] at hF
        rcases hF with (hFant | hFsucc)
        · rcases hFant with hFx | hFleafAnt
          · rw [hFx] at hj
            exact hLeafFV (FormulaN.impl X Y) hBInList j (Or.inl hj)
          · exact hLeafFV F (mem_antSucc_of_mem_antecedent hFleafAnt) j hj
        · rcases hFsucc with (hFsucc1 | hFΛ)
          · rcases hFsucc1 with hFeqY | hFΔ
            · rw [hFeqY] at hj
              exact hLeafFV (FormulaN.impl X Y) hBInList j (Or.inr hj)
            · have hFleaf : F ∈ leaf.succedent := by
                rw [hSplit]
                exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΔ)))
              exact hLeafFV F (mem_antSucc_of_mem_succedent hFleaf) j hj
          · have hFleaf : F ∈ leaf.succedent := by
              rw [hSplit]
              exact List.mem_append.mpr (Or.inr hFΛ)
            exact hLeafFV F (mem_antSucc_of_mem_succedent hFleaf) j hj
      · intro F hF y hy
        simp only [List.mem_append, List.mem_singleton] at hF
        rcases hF with (hFant | hFsucc)
        · rcases hFant with hFx | hFleafAnt
          · rw [hFx] at hy
            exact hLeafBVSub (FormulaN.impl X Y) hBInList y (Or.inl hy)
          · exact hLeafBVSub F (mem_antSucc_of_mem_antecedent hFleafAnt) y hy
        · rcases hFsucc with (hFsucc1 | hFΛ)
          · rcases hFsucc1 with hFeqY | hFΔ
            · rw [hFeqY] at hy
              exact hLeafBVSub (FormulaN.impl X Y) hBInList y (Or.inr hy)
            · have hFleaf : F ∈ leaf.succedent := by
                rw [hSplit]
                exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΔ)))
              exact hLeafBVSub F (mem_antSucc_of_mem_succedent hFleaf) y hy
          · have hFleaf : F ∈ leaf.succedent := by
              rw [hSplit]
              exact List.mem_append.mpr (Or.inr hFΛ)
            exact hLeafBVSub F (mem_antSucc_of_mem_succedent hFleaf) y hy
    next X hBcase =>
      -- neg case: antecedent = [X]++leaf.antecedent, succedent = Δ++Λ
      simp only [growRightOneProp, TreeLeafInv, SearchTree.toDeductionTree]
      intro l hl
      simp only [leaves_cast] at hl
      simp only [SearchTree.toDeductionTree, GDeductionTreeExt.leaves_onePremise,
                 GDeductionTreeExt.leaves_leaf,
                 List.mem_singleton] at hl
      subst hl
      have hSplit := (splitListAt leaf.succedent (FormulaN.neg X) hBcase).property
      have hBInList : FormulaN.neg X ∈ leaf.antecedent ++ leaf.succedent :=
        mem_antSucc_of_mem_succedent hBcase
      constructor
      · intro F hF j hj
        simp only [List.mem_append, List.mem_singleton] at hF
        rcases hF with (hFant | hFsucc)
        · rcases hFant with hFx | hFleafAnt
          · rw [hFx] at hj
            exact hLeafFV (FormulaN.neg X) hBInList j hj
          · exact hLeafFV F (mem_antSucc_of_mem_antecedent hFleafAnt) j hj
        · have hFleaf : F ∈ leaf.succedent := by
            rw [hSplit]
            rcases hFsucc with hFΔ | hFΛ
            · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΔ)))
            · exact List.mem_append.mpr (Or.inr hFΛ)
          exact hLeafFV F (mem_antSucc_of_mem_succedent hFleaf) j hj
      · intro F hF y hy
        simp only [List.mem_append, List.mem_singleton] at hF
        rcases hF with (hFant | hFsucc)
        · rcases hFant with hFx | hFleafAnt
          · rw [hFx] at hy
            exact hLeafBVSub (FormulaN.neg X) hBInList y hy
          · exact hLeafBVSub F (mem_antSucc_of_mem_antecedent hFleafAnt) y hy
        · have hFleaf : F ∈ leaf.succedent := by
            rw [hSplit]
            rcases hFsucc with hFΔ | hFΛ
            · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΔ)))
            · exact List.mem_append.mpr (Or.inr hFΛ)
          exact hLeafBVSub F (mem_antSucc_of_mem_succedent hFleaf) y hy
    next =>
      -- predN case: no-op
      simp only [TreeLeafInv, SearchTree.toDeductionTree, GDeductionTreeExt.leaves_leaf]
      intro l hl
      simp only [List.mem_singleton] at hl
      subst hl
      exact ⟨hLeafFV, hLeafBVSub⟩
    next =>
      -- eq_ case: no-op
      simp only [TreeLeafInv, SearchTree.toDeductionTree, GDeductionTreeExt.leaves_leaf]
      intro l hl
      simp only [List.mem_singleton] at hl
      subst hl
      exact ⟨hLeafFV, hLeafBVSub⟩
    next x C hBcase =>
      -- ex case: growRightExInv
      simp only [TreeLeafInv, SearchTree.toDeductionTree]
      unfold growRightExInv
      simp only
      classical
      by_cases hEmpty :
        ((st.tTERM0.mapIdx (fun k t => (t, k))).filter
          (fun p => ¬ SearchState.isUsed records p.2 (FormulaN.ex x C))).map Prod.fst = []
      · simp only [hEmpty, dif_pos, SearchTree.toDeductionTree, GDeductionTreeExt.leaves_leaf]
        intro l hl
        simp only [List.mem_singleton] at hl
        subst hl
        exact ⟨hLeafFV, hLeafBVSub⟩
      · rw [dif_neg hEmpty]
        intro l hl
        simp only [leaves_cast] at hl
        simp only [SearchTree.toDeductionTree, GDeductionTreeExt.leaves_onePremise,
                   GDeductionTreeExt.leaves_leaf,
                   List.mem_singleton] at hl
        subst hl
        have hSplit := (splitListAt leaf.succedent (FormulaN.ex x C) hBcase).property
        have hExInList : FormulaN.ex x C ∈ leaf.antecedent ++ leaf.succedent :=
          mem_antSucc_of_mem_succedent hBcase
        constructor
        · -- LeafFVBelow supply
          intro F hF j hj
          simp only [List.mem_append, List.mem_singleton] at hF
          rcases hF with (hFant | hFsucc)
          · exact hLeafFV F (mem_antSucc_of_mem_antecedent hFant) j hj
          · rcases hFsucc with (hFsucc1 | hFΛ)
            · rcases hFsucc1 with (hFΔ_or_ts | hFExEq)
              · rcases hFΔ_or_ts with hFΔ | hFts
                · have hFleaf : F ∈ leaf.succedent := by
                    rw [hSplit]
                    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΔ)))
                  exact hLeafFV F (mem_antSucc_of_mem_succedent hFleaf) j hj
                · rw [List.mem_map] at hFts
                  obtain ⟨t, htTS, htF⟩ := hFts
                  subst htF
                  have hjCases := formulaFVN_formulaSubstN C t x j hj
                  rcases hjCases with ⟨hjC, hjne⟩ | hjT
                  · have hjEx : j ∈ formulaFVN (FormulaN.ex x C) :=
                      ⟨hjC, fun heq => hjne heq⟩
                    exact hLeafFV (FormulaN.ex x C) hExInList j hjEx
                  · have htTTERM0 : t ∈ st.tTERM0 := by
                      unfold SearchState.tTERM0
                      rw [List.mem_map] at htTS
                      obtain ⟨p, hpFilt, hpt⟩ := htTS
                      have hpIdx : p ∈ (st.TERM0.mapIdx (fun k t => (t, k))) :=
                        (List.mem_filter.mp hpFilt).1
                      rw [List.mem_mapIdx] at hpIdx
                      obtain ⟨i, hi, hpEq⟩ := hpIdx
                      have h1 : (st.TERM0[i], i) = p := hpEq
                      have h2 : p.1 = st.TERM0[i] := congrArg Prod.fst h1.symm
                      rw [← hpt, h2]
                      exact List.getElem_mem hi
                    exact termFV_of_tTERM0_lt_availNext hNoFunc hInv htTTERM0 j hjT
              · rw [hFExEq] at hj
                exact hLeafFV (FormulaN.ex x C) hExInList j hj
            · have hFleaf : F ∈ leaf.succedent := by
                rw [hSplit]
                exact List.mem_append.mpr (Or.inr hFΛ)
              exact hLeafFV F (mem_antSucc_of_mem_succedent hFleaf) j hj
        · -- LeafBVSubsetSeq
          intro F hF y hy
          simp only [List.mem_append, List.mem_singleton] at hF
          rcases hF with (hFant | hFsucc)
          · exact hLeafBVSub F (mem_antSucc_of_mem_antecedent hFant) y hy
          · rcases hFsucc with (hFsucc1 | hFΛ)
            · rcases hFsucc1 with (hFΔ_or_ts | hFExEq)
              · rcases hFΔ_or_ts with hFΔ | hFts
                · have hFleaf : F ∈ leaf.succedent := by
                    rw [hSplit]
                    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΔ)))
                  exact hLeafBVSub F (mem_antSucc_of_mem_succedent hFleaf) y hy
                · rw [List.mem_map] at hFts
                  obtain ⟨t, _, htF⟩ := hFts
                  rw [← htF] at hy
                  have hyC : y ∈ formulaBVN C :=
                    @formulaBVN_formulaSubstN_subset _ C t x y hy
                  have hyEx : y ∈ formulaBVN (FormulaN.ex x C) := Or.inl hyC
                  exact hLeafBVSub (FormulaN.ex x C) hExInList y hyEx
              · rw [hFExEq] at hy
                exact hLeafBVSub (FormulaN.ex x C) hExInList y hy
            · have hFleaf : F ∈ leaf.succedent := by
                rw [hSplit]
                exact List.mem_append.mpr (Or.inr hFΛ)
              exact hLeafBVSub F (mem_antSucc_of_mem_succedent hFleaf) y hy
    next x C hBcase =>
      -- all case: growRightAllInv
      simp only [TreeLeafInv, SearchTree.toDeductionTree]
      unfold growRightAllInv
      simp only
      intro l hl
      simp only [leaves_cast] at hl
      simp only [SearchTree.toDeductionTree, GDeductionTreeExt.leaves_onePremise,
                 GDeductionTreeExt.leaves_leaf,
                 List.mem_singleton] at hl
      subst hl
      have hSplit := (splitListAt leaf.succedent (FormulaN.all x C) hBcase).property
      have hAllInList : FormulaN.all x C ∈ leaf.antecedent ++ leaf.succedent :=
        mem_antSucc_of_mem_succedent hBcase
      -- new availNext = st.availNext + 1
      constructor
      · intro F hF j hj
        simp only [List.mem_append, List.mem_singleton] at hF
        rcases hF with (hFant | hFsucc)
        · have h := hLeafFV F (mem_antSucc_of_mem_antecedent hFant) j hj
          exact BeforeCursor.mono h (Nat.le_succ _)
        · rcases hFsucc with (hFsucc1 | hFΛ)
          · rcases hFsucc1 with hFΔ | hFeqSubst
            · have hFleaf : F ∈ leaf.succedent := by
                rw [hSplit]
                exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΔ)))
              have h := hLeafFV F (mem_antSucc_of_mem_succedent hFleaf) j hj
              exact BeforeCursor.mono h (Nat.le_succ _)
            · rw [hFeqSubst] at hj
              have hjCases := formulaFVN_formulaSubstN C (Term.var (supply.varAt st.availNext (hInv.available_vars st.availNext))) x j hj
              rcases hjCases with ⟨hjC, hjne⟩ | hjT
              · have hjAll : j ∈ formulaFVN (FormulaN.all x C) :=
                  ⟨hjC, fun heq => hjne heq⟩
                have h := hLeafFV (FormulaN.all x C) hAllInList j hjAll
                exact BeforeCursor.mono h (Nat.le_succ _)
              · have hj_eq : j = supply.varAt st.availNext (hInv.available_vars st.availNext) := hjT
                subst hj_eq
                exact supply.varAt_beforeSucc st.availNext (hInv.available_vars st.availNext)
          · have hFleaf : F ∈ leaf.succedent := by
              rw [hSplit]
              exact List.mem_append.mpr (Or.inr hFΛ)
            have h := hLeafFV F (mem_antSucc_of_mem_succedent hFleaf) j hj
            exact BeforeCursor.mono h (Nat.le_succ _)
      · intro F hF y hy
        simp only [List.mem_append, List.mem_singleton] at hF
        rcases hF with (hFant | hFsucc)
        · exact hLeafBVSub F (mem_antSucc_of_mem_antecedent hFant) y hy
        · rcases hFsucc with (hFsucc1 | hFΛ)
          · rcases hFsucc1 with hFΔ | hFeqSubst
            · have hFleaf : F ∈ leaf.succedent := by
                rw [hSplit]
                exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hFΔ)))
              exact hLeafBVSub F (mem_antSucc_of_mem_succedent hFleaf) y hy
            · rw [hFeqSubst] at hy
              have hyC : y ∈ formulaBVN C :=
                @formulaBVN_formulaSubstN_subset _ C (Term.var (supply.varAt st.availNext (hInv.available_vars st.availNext))) x y hy
              have hyAll : y ∈ formulaBVN (FormulaN.all x C) := Or.inl hyC
              exact hLeafBVSub (FormulaN.all x C) hAllInList y hyAll
          · have hFleaf : F ∈ leaf.succedent := by
              rw [hSplit]
              exact List.mem_append.mpr (Or.inr hFΛ)
            exact hLeafBVSub F (mem_antSucc_of_mem_succedent hFleaf) y hy
  next hB =>
    -- B ∉ leaf.succedent: no-op
    simp only [TreeLeafInv, SearchTree.toDeductionTree, GDeductionTreeExt.leaves_leaf]
    intro l hl
    simp only [List.mem_singleton] at hl
    subst hl
    exact ⟨hLeafFV, hLeafBVSub⟩

end LCS.FirstOrder.Gentzen.Search.NoFunction
end

