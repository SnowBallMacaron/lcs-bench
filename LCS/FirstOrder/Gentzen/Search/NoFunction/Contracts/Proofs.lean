import LCS.FirstOrder.Gentzen.Search.NoFunction.Contracts

section

namespace LCS.FirstOrder.Gentzen.Search.NoFunction

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.FirstOrder.Gentzen LCS.FirstOrder.Gentzen.Hintikka

proof_of exists_renamingApart := by
  let forms := seq.antecedent ++ seq.succedent
  let n := (forms.map formulaMaxVarN).foldl Nat.max 0 + 1
  let ren := fun (A : FormulaN L) => (rectifyAux A id n).1
  let variant : Sequent L := ⟨seq.antecedent.map ren, seq.succedent.map ren⟩
  have hFresh : ∀ A ∈ forms, ∀ x, x ∈ formulaFVN A → x < n := by
    intro A hA x hx
    have hmax := mem_le_foldl_max (xs := forms.map formulaMaxVarN)
      (List.mem_map.mpr ⟨A, hA, rfl⟩) 0
    exact Nat.lt_succ_of_le (Nat.le_trans (formulaFVN_le_maxVarN A x hx) hmax)
  refine ⟨n, variant, rfl, rfl, ?_, ?_⟩
  · intro A hA M s
    exact rectifyAux_eval A id n (hFresh A hA) M s
  · have hmap : variant.antecedent ++ variant.succedent = forms.map ren := by
      simp only [variant, forms, List.map_append]
    intro x ⟨F, hF, hx⟩ B hB hBound
    rw [hmap] at hF hB
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hF
    obtain ⟨C, _, rfl⟩ := List.mem_map.mp hB
    obtain ⟨y, hy, hxy⟩ := rectifyAux_fv_source A id n x hx
    have hxlt : x < n := hxy.symm ▸ hFresh A hA y hy
    have hxge := (rectifyAux_bv_range C id n x hBound).1
    omega


end LCS.FirstOrder.Gentzen.Search.NoFunction

end

section

namespace LCS.FirstOrder.Gentzen.Search.NoFunction

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.Gentzen LCS.FirstOrder.Gentzen.Hintikka

helper /-- The actual grow-LeftAll instance uses exactly the terms selected from the round snapshots. -/
theorem growLeftAllInv_instanceTerms {L : Language} {supply : TermStream L}
    (hNoFunc : L.funSymbols → False) {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq) (x : Nat) (A : FormulaN L) (leaf : Sequent L)
    (hA : FormulaN.all x A ∈ leaf.antecedent) (hSub : LeafBVSubsetSeq leaf seq)
    (st : SearchState L supply) (records : BranchRecords L) (hInv : SearchState.Inv seq bound st) :
    (growLeftAllInv hNoFunc hCNFB x A leaf hA hSub st records hInv).1.rootInstanceTerms =
      (if st.instanceTerms records (.all x A) = [] then none else
        some (st.instanceTerms records (.all x A))) := by
  classical
  unfold growLeftAllInv SearchState.instanceTerms
  dsimp only
  split <;> rename_i h
  · simp only [h, dif_pos, if_pos]
    rfl
  · simp only [h, dif_neg, if_neg]
    rw [SearchTree.rootInstanceTerms_cast]
    rfl

helper /-- The actual grow-RightEx instance uses exactly the terms selected from the round snapshots. -/
theorem growRightExInv_instanceTerms {L : Language} {supply : TermStream L}
    (hNoFunc : L.funSymbols → False) {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq) (x : Nat) (A : FormulaN L) (leaf : Sequent L)
    (hA : FormulaN.ex x A ∈ leaf.succedent) (hSub : LeafBVSubsetSeq leaf seq)
    (st : SearchState L supply) (records : BranchRecords L) (hInv : SearchState.Inv seq bound st) :
    (growRightExInv hNoFunc hCNFB x A leaf hA hSub st records hInv).1.rootInstanceTerms =
      (if st.instanceTerms records (.ex x A) = [] then none else
        some (st.instanceTerms records (.ex x A))) := by
  classical
  unfold growRightExInv SearchState.instanceTerms
  dsimp only
  split <;> rename_i h
  · simp only [h, dif_pos, if_pos]
    rfl
  · simp only [h, dif_neg, if_neg]
    rw [SearchTree.rootInstanceTerms_cast]
    rfl

helper /-- Definition 5.4.9 (companion): Two instance steps on the same principal
    formula with the same round snapshots use identical term lists. -/
theorem growLeftAllInv_same_substitutions {L : Language} {supply : TermStream L}
    (hNoEq : L.hasEquality = false)
    (hNoFunc : L.funSymbols → False) {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq) (x : Nat) (A : FormulaN L)
    (leaf leaf' : Sequent L)
    (hA : FormulaN.all x A ∈ leaf.antecedent)
    (hA' : FormulaN.all x A ∈ leaf'.antecedent)
    (hSub : LeafBVSubsetSeq leaf seq) (hSub' : LeafBVSubsetSeq leaf' seq)
    (st st' : SearchState L supply) (records records' : BranchRecords L)
    (hInv : SearchState.Inv seq bound st) (hInv' : SearchState.Inv seq bound st')
    (hTerms : st.TERM0 = st'.TERM0) (hRecords : records.form0 = records'.form0) :
    (growLeftAllInv hNoFunc hCNFB x A leaf hA hSub st records hInv).1.rootInstanceTerms =
      (growLeftAllInv hNoFunc hCNFB x A leaf' hA' hSub' st' records' hInv').1.rootInstanceTerms := by
  rw [growLeftAllInv_instanceTerms, growLeftAllInv_instanceTerms,
    SearchState.instanceTerms_eq st st' records records' (.all x A) hTerms hRecords]

helper /-- Definition 5.4.9 (companion): Two instance steps on the same principal
    formula with the same round snapshots use identical term lists. -/
theorem growRightExInv_same_substitutions {L : Language} {supply : TermStream L}
    (hNoEq : L.hasEquality = false)
    (hNoFunc : L.funSymbols → False) {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq) (x : Nat) (A : FormulaN L)
    (leaf leaf' : Sequent L)
    (hA : FormulaN.ex x A ∈ leaf.succedent)
    (hA' : FormulaN.ex x A ∈ leaf'.succedent)
    (hSub : LeafBVSubsetSeq leaf seq) (hSub' : LeafBVSubsetSeq leaf' seq)
    (st st' : SearchState L supply) (records records' : BranchRecords L)
    (hInv : SearchState.Inv seq bound st) (hInv' : SearchState.Inv seq bound st')
    (hTerms : st.TERM0 = st'.TERM0) (hRecords : records.form0 = records'.form0) :
    (growRightExInv hNoFunc hCNFB x A leaf hA hSub st records hInv).1.rootInstanceTerms =
      (growRightExInv hNoFunc hCNFB x A leaf' hA' hSub' st' records' hInv').1.rootInstanceTerms := by
  rw [growRightExInv_instanceTerms, growRightExInv_instanceTerms,
    SearchState.instanceTerms_eq st st' records records' (.ex x A) hTerms hRecords]

end LCS.FirstOrder.Gentzen.Search.NoFunction

end
