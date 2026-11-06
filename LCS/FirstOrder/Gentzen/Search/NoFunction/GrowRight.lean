import LCS.Item
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.Hintikka
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics.Subformulae
import LCS.FirstOrder.Gentzen.Search.NoFunction.LeafExtension
import Attach
import LCS.FirstOrder.Gentzen.Search.NoFunction.GrowRight.ProofsStamp

/-! # Procedure grow-right (Definition 5.4.9)

The right rules applied at a leaf (propositional connectives, exists:right with the
terms of TERM₀, for-all:right with head(AVAIL₀)), their effect on the search state,
and grow-right on every nonaxiom leaf of a tree.
Source: Logic for Computer Science, Gallier 2015
-/

section
namespace LCS.FirstOrder.Gentzen.Search.NoFunction
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka

/-- Definition 5.4.9 (companion, `grow-right` propositional cases):
    Dual of `growLeftOneProp` — given a principal succedent formula
    `B` occurring in a single leaf sequent `leaf`, build the subtree
    produced by applying the G-rule whose principal formula on the
    right is `B`.

    Textbook §5.4.9 (grow-right procedure):
    - `B = X ∧ Y`  : two-premise ∧:right rule.
    - `B = X ∨ Y`  : one-premise ∨:right rule.
    - `B = X ⊃ Y`  : one-premise ⊃:right rule.
    - `B = ¬X`     : one-premise ¬:right rule.
    - `B = ∀x C` / `B = ∃x C`  : quantifier cases (handled by
      `growRightOneQuant` below).
    - `B` atomic  : no-op. -/
@[blueprint "chap5__definition_5_4_9"]
noncomputable def growRightOneProp {L : Language} {supply : TermStream L}
    (B : FormulaN L) (leaf : Sequent L)
    (hB : B ∈ leaf.succedent) (st : SearchState L supply) (records : BranchRecords L) :
    SearchTree leaf × SearchState L supply :=
  match hBcase : B with
  | .conj X Y =>
      have hBin : FormulaN.conj X Y ∈ leaf.succedent := hBcase ▸ hB
      let split := splitListAt leaf.succedent (FormulaN.conj X Y) hBin
      let Δ := split.val.1
      let Λ := split.val.2
      let conc : Sequent L := Sequent.mk leaf.antecedent (Δ ++ [FormulaN.conj X Y] ++ Λ)
      let premL : Sequent L := Sequent.mk leaf.antecedent (Δ ++ [X] ++ Λ)
      let premR : Sequent L := Sequent.mk leaf.antecedent (Δ ++ [Y] ++ Λ)
      let rule : GentzenStep2Ext premL premR conc :=
        GentzenStep2Ext.conjRight leaf.antecedent Δ Λ X Y
      let t' : SearchTree conc :=
        SearchTree.twoPremise rule
          (SearchTree.leaf premL records) (SearchTree.leaf premR records)
      have hConc : conc = leaf := by
        show Sequent.mk _ _ = leaf
        congr 1
        exact split.property.symm
      (hConc ▸ t', st)
  | .disj X Y =>
      have hBin : FormulaN.disj X Y ∈ leaf.succedent := hBcase ▸ hB
      let split := splitListAt leaf.succedent (FormulaN.disj X Y) hBin
      let Δ := split.val.1
      let Λ := split.val.2
      let conc : Sequent L := Sequent.mk leaf.antecedent (Δ ++ [FormulaN.disj X Y] ++ Λ)
      let prem : Sequent L := Sequent.mk leaf.antecedent (Δ ++ [X, Y] ++ Λ)
      let rule : GentzenStep1Ext prem conc := GentzenStep1Ext.disjRight leaf.antecedent Δ Λ X Y
      let t' : SearchTree conc :=
        SearchTree.onePremise rule (SearchTree.leaf prem records)
      have hConc : conc = leaf := by
        show Sequent.mk _ _ = leaf
        congr 1
        exact split.property.symm
      (hConc ▸ t', st)
  | .impl X Y =>
      have hBin : FormulaN.impl X Y ∈ leaf.succedent := hBcase ▸ hB
      let split := splitListAt leaf.succedent (FormulaN.impl X Y) hBin
      let Δ := split.val.1
      let Λ := split.val.2
      let conc : Sequent L := Sequent.mk leaf.antecedent (Δ ++ [FormulaN.impl X Y] ++ Λ)
      let prem : Sequent L := Sequent.mk ([X] ++ leaf.antecedent) ([Y] ++ Δ ++ Λ)
      let rule : GentzenStep1Ext prem conc := GentzenStep1Ext.implRight leaf.antecedent Δ Λ X Y
      let t' : SearchTree conc :=
        SearchTree.onePremise rule (SearchTree.leaf prem records)
      have hConc : conc = leaf := by
        show Sequent.mk _ _ = leaf
        congr 1
        exact split.property.symm
      (hConc ▸ t', st)
  | .neg X =>
      have hBin : FormulaN.neg X ∈ leaf.succedent := hBcase ▸ hB
      let split := splitListAt leaf.succedent (FormulaN.neg X) hBin
      let Δ := split.val.1
      let Λ := split.val.2
      let conc : Sequent L := Sequent.mk leaf.antecedent (Δ ++ [FormulaN.neg X] ++ Λ)
      let prem : Sequent L := Sequent.mk ([X] ++ leaf.antecedent) (Δ ++ Λ)
      let rule : GentzenStep1Ext prem conc := GentzenStep1Ext.negRight leaf.antecedent Δ Λ X
      let t' : SearchTree conc :=
        SearchTree.onePremise rule (SearchTree.leaf prem records)
      have hConc : conc = leaf := by
        show Sequent.mk _ _ = leaf
        congr 1
        exact split.property.symm
      (hConc ▸ t', st)
  -- atomic / quantifier / `eq_` cases: no propositional rule applies.
  | .predN _ _ => (SearchTree.leaf leaf records, st)
  | .eq_ _ _ _ => (SearchTree.leaf leaf records, st)
  | .all _ _ => (SearchTree.leaf leaf records, st)
  | .ex _ _ => (SearchTree.leaf leaf records, st)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 5.4.9 (companion, discharge — leaf-level): Mirror of
    `term_isFreeForN_body_all_of_Inv_Sub` for the existential body. -/
theorem SearchState.term_isFreeForN_body_ex_of_Inv_Sub {L : Language} {supply : TermStream L}
    (hNoFunc : L.funSymbols → False)
    {seq leaf : Sequent L} {bound : Nat} {st : SearchState L supply}
    (h : SearchState.Inv seq bound st)
    (hCNFB : crossNoFreeBound seq)
    (hSub : LeafBVSubsetSeq leaf seq)
    {u : Term L} (hu : u ∈ st.tTERM0)
    (z : Nat) (A : FormulaN L)
    (hInLeaf : FormulaN.ex z A ∈ leaf.antecedent ++ leaf.succedent) :
    ∀ y, isFreeForN u y A := by
-- BEGIN PROOF
  intro y
  unfold tTERM0 at hu
  match u with
  | .var i =>
    have hAllowed := h.terms_allowed _ hu i rfl
    have hNotBVSeq : ∀ G ∈ seq.antecedent ++ seq.succedent,
        i ∉ formulaBVN G := fun G hG =>
      notBV_of_allowed hCNFB h.bound_above_seq hAllowed G hG
    have hNotBV_ex : i ∉ formulaBVN (FormulaN.ex z A) :=
      notBV_leaf_of_notBV_seq hSub hNotBVSeq _ hInLeaf
    have hNotBV_A : i ∉ formulaBVN A := notBV_body_of_ex hNotBV_ex
    exact isFreeForN_var_of_notBV i y A hNotBV_A
  | .const c => exact isFreeForN_const c y A
  | .func f _ => exact (hNoFunc f).elim

/-- Definition 5.4.9 (companion, `grow-right` ∃x C case, invariant-aware):
    Mirror of `growLeftAllInv` for ∃:right. Given `∃x C ∈ leaf.succedent`
    and `LeafBVSubsetSeq leaf seq`, apply the extended ∃:right rule
    using the terms of `tTERM0 st` whose branch FORM₀ lacks the principal
    formula. The child inherits the updated branch FORM₁; FORM₀ and the
    global state are unchanged.

    Textbook §5.4.9 grow-right (∃x C case, lines 181-188):
    "for every term u_k ∈ t(TERM₀) such that A is not in FORM₀(k) do
     extend every nonaxiom leaf of S by applying the ∃ : right rule
     using the term u_k as one of the terms of the rule.
     In TERM₁ let FORM₁(k) := append(FORM₁(k), A)". -/
@[blueprint "chap5__definition_5_4_9"]
noncomputable def growRightExInv {L : Language} {supply : TermStream L}
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq)
    (x : Nat) (C : FormulaN L) (leaf : Sequent L)
    (hB : FormulaN.ex x C ∈ leaf.succedent)
    (hLeafBVSub : LeafBVSubsetSeq leaf seq)
    (st : SearchState L supply) (records : BranchRecords L)
    (hInv : SearchState.Inv seq bound st) :
    SearchTree leaf × SearchState L supply := by
  classical
  let indexedTerms : List (Term L × Nat) :=
    st.tTERM0.mapIdx (fun k t => (t, k))
  let filtered : List (Term L × Nat) :=
    indexedTerms.filter (fun p => ¬ SearchState.isUsed records p.2 (FormulaN.ex x C))
  let ts : List (Term L) := filtered.map Prod.fst
  let ks : List Nat := filtered.map Prod.snd
  by_cases hEmpty : ts = []
  · exact (SearchTree.leaf leaf records, st)
  · have hne : ts ≠ [] := hEmpty
    have hExInLeafList :
        FormulaN.ex x C ∈ leaf.antecedent ++ leaf.succedent :=
      List.mem_append.mpr (Or.inr hB)
    have hfree : ∀ t ∈ ts, isFreeForN t x C := by
      intro t ht
      have hInTTERM0 : t ∈ st.tTERM0 := by
        rw [List.mem_map] at ht
        obtain ⟨p, hpFilt, hpt⟩ := ht
        have hpIdx : p ∈ indexedTerms := (List.mem_filter.mp hpFilt).1
        rw [List.mem_mapIdx] at hpIdx
        obtain ⟨i, hi, hpEq⟩ := hpIdx
        show t ∈ st.TERM0
        have h1 : (st.TERM0[i], i) = p := hpEq
        have h2 : p.1 = st.TERM0[i] := congrArg Prod.fst h1.symm
        rw [← hpt, h2]
        exact List.getElem_mem hi
      exact SearchState.term_isFreeForN_body_ex_of_Inv_Sub
              hNoFunc hInv hCNFB hLeafBVSub hInTTERM0 x C hExInLeafList x
    let split := splitListAt leaf.succedent (FormulaN.ex x C) hB
    let Δ := split.val.1
    let Λ := split.val.2
    let Γ := leaf.antecedent
    let conc : Sequent L := Sequent.mk Γ (Δ ++ [FormulaN.ex x C] ++ Λ)
    let prem : Sequent L :=
      Sequent.mk Γ
        (Δ ++ ts.map (fun t => formulaSubstN C t x) ++ [FormulaN.ex x C] ++ Λ)
    let rule : GentzenStep1Ext prem conc :=
      GentzenStep1Ext.exRight ts Γ Δ Λ x C hne hfree
    let records' : BranchRecords L :=
      ks.foldl (fun r k => SearchState.appendFORM1 r k (FormulaN.ex x C)) records
    let t' : SearchTree conc :=
      SearchTree.onePremise rule (SearchTree.leaf prem records')
    have hConc : conc = leaf := by
      show Sequent.mk _ _ = leaf
      congr 1
      exact split.property.symm
    exact (hConc ▸ t', st)

/-- Definition 5.4.9 (companion, `grow-right` ∀x C case, invariant-aware):
    Mirror of `growLeftExInv` for ∀:right. Given `∀x C ∈ leaf.succedent`,
    apply the ∀:right rule with eigenvariable `y := head(AVAIL₀)`.
    The global state is unchanged; the tree-level caller activates y once.
    Freshness and free-for discharged from state invariant +
    LeafFVBelow + LeafBVBelow.

    Textbook §5.4.9 grow-right (∀x C case, lines 191-196). -/
@[blueprint "chap5__definition_5_4_9"]
noncomputable def growRightAllInv {L : Language} {supply : TermStream L}
    {seq : Sequent L} {bound : Nat}
    (x : Nat) (C : FormulaN L) (leaf : Sequent L)
    (hB : FormulaN.all x C ∈ leaf.succedent)
    (st : SearchState L supply) (records : BranchRecords L) (hInv : SearchState.Inv seq bound st)
    (hLeafFV : LeafFVBelow supply leaf st.availNext)
    (hLeafBV : LeafBVBelow leaf bound)
    (hLeafBVSub : LeafBVSubsetSeq leaf seq) :
    SearchTree leaf × SearchState L supply := by
  let y : Nat := supply.varAt st.availNext (hInv.available_vars st.availNext)
  have hy : supply.entries st.availNext = some (.var y) :=
    supply.varAt_spec st.availNext (hInv.available_vars st.availNext)
  let split := splitListAt leaf.succedent (FormulaN.all x C) hB
  let Δ := split.val.1
  let Λ := split.val.2
  let Γ := leaf.antecedent
  have hfresh :
      ∀ F ∈ (Sequent.mk Γ (Δ ++ [FormulaN.all x C] ++ Λ)).antecedent ++
            (Sequent.mk Γ (Δ ++ [FormulaN.all x C] ++ Λ)).succedent,
        y ∉ formulaFVN F := by
    intro F hF
    have hFInLeaf : F ∈ leaf.antecedent ++ leaf.succedent := by
      rcases List.mem_append.mp hF with hAnt | hSucc
      · exact List.mem_append.mpr (Or.inl hAnt)
      · have hEq : Δ ++ [FormulaN.all x C] ++ Λ = leaf.succedent :=
          split.property.symm
        exact List.mem_append.mpr (Or.inr (hEq ▸ hSucc))
    intro hYin
    exact hLeafFV F hFInLeaf y hYin st.availNext (Nat.le_refl _) hy
  have hAllInLeafList :
      FormulaN.all x C ∈ leaf.antecedent ++ leaf.succedent := by
    exact List.mem_append.mpr (Or.inr hB)
  have hYnotBV_C : y ∉ formulaBVN C :=
    notBV_body_of_all (notBV_leaf_of_notBV_seq hLeafBVSub
      (hInv.avail_fresh st.availNext (Nat.le_refl _) y hy) _ hAllInLeafList)
  have hfreeFor : isFreeForN (Term.var y) x C :=
    isFreeForN_var_of_notBV y x C hYnotBV_C
  let conc : Sequent L := Sequent.mk Γ (Δ ++ [FormulaN.all x C] ++ Λ)
  let prem : Sequent L :=
    Sequent.mk Γ (Δ ++ [formulaSubstN C (Term.var y) x] ++ Λ)
  let rule : GentzenStep1Ext prem conc :=
    GentzenStep1Ext.allRight y Γ Δ Λ x C hfresh hfreeFor
  let t' : SearchTree conc :=
    SearchTree.onePremise rule (SearchTree.leaf prem records)
  have hConc : conc = leaf := by
    show Sequent.mk _ _ = leaf
    congr 1
    exact split.property.symm
  exact (hConc ▸ t', st)

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- `growRightOneProp` leaves `SearchState` unchanged. -/
theorem growRightOneProp_state_eq {L : Language} {supply : TermStream L} (B : FormulaN L)
    (leaf : Sequent L) (hB : B ∈ leaf.succedent) (st : SearchState L supply) (records : BranchRecords L) :
    (growRightOneProp B leaf hB st records).2 = st := by
-- BEGIN PROOF
  unfold growRightOneProp; split <;> rfl

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- `growRightExInv` preserves `Inv`. -/
theorem growRightExInv_preserves_Inv {L : Language} {supply : TermStream L}
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq)
    (x : Nat) (C : FormulaN L) (leaf : Sequent L)
    (hB : FormulaN.ex x C ∈ leaf.succedent)
    (hLeafBVSub : LeafBVSubsetSeq leaf seq)
    (st : SearchState L supply) (records : BranchRecords L) (hInv : SearchState.Inv seq bound st) :
    SearchState.Inv seq bound
      (growRightExInv hNoFunc hCNFB x C leaf hB hLeafBVSub st records hInv).2 := by
  classical
  unfold growRightExInv
  dsimp only
  split <;> exact hInv

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- `growRightOneProp` doesn't touch `availNext`. -/
theorem growRightOneProp_availNext_eq {L : Language} {supply : TermStream L} (B : FormulaN L)
    (leaf : Sequent L) (hB : B ∈ leaf.succedent) (st : SearchState L supply) (records : BranchRecords L) :
    (growRightOneProp B leaf hB st records).2.availNext = st.availNext := by
-- BEGIN PROOF
  rw [growRightOneProp_state_eq]

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- `growRightExInv` doesn't touch `availNext`. -/
theorem growRightExInv_availNext_eq {L : Language} {supply : TermStream L}
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq)
    (x : Nat) (C : FormulaN L) (leaf : Sequent L)
    (hB : FormulaN.ex x C ∈ leaf.succedent)
    (hLeafBVSub : LeafBVSubsetSeq leaf seq)
    (st : SearchState L supply) (records : BranchRecords L) (hInv : SearchState.Inv seq bound st) :
    (growRightExInv hNoFunc hCNFB x C leaf hB hLeafBVSub st records hInv).2.availNext
      = st.availNext := by
  classical
  unfold growRightExInv
  dsimp only
  split <;> rfl

/-- Definition 5.4.9 (companion, `grow-right` at a leaf): Dispatch on
    principal succedent formula `B`'s main connective and apply the
    matching grow-* primitive. Mirror of `growLeftAtLeaf`. -/
@[blueprint "chap5__definition_5_4_9"]
noncomputable def growRightAtLeaf {L : Language} {supply : TermStream L} (hNoEq : L.hasEquality = false)
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq)
    (B : FormulaN L) (leaf : Sequent L)
    (st : SearchState L supply) (records : BranchRecords L) (hInv : SearchState.Inv seq bound st)
    (hLeafFV : LeafFVBelow supply leaf st.availNext)
    (hLeafBV : LeafBVBelow leaf bound)
    (hLeafBVSub : LeafBVSubsetSeq leaf seq) :
    SearchTree leaf × SearchState L supply := by
  classical
  by_cases hB : B ∈ leaf.succedent
  · match B, hB with
    | .conj _ _, hB => exact growRightOneProp _ leaf hB st records
    | .disj _ _, hB => exact growRightOneProp _ leaf hB st records
    | .impl _ _, hB => exact growRightOneProp _ leaf hB st records
    | .neg _, hB => exact growRightOneProp _ leaf hB st records
    | .predN _ _, _ => exact (SearchTree.leaf leaf records, st)
    | .eq_ _ _ _, _ => exact (SearchTree.leaf leaf records, st)
    | .ex x C, hB =>
        exact growRightExInv hNoFunc hCNFB x C leaf hB hLeafBVSub st records hInv
    | .all x C, hB =>
        exact ((growRightAllInv x C leaf hB st records hInv hLeafFV hLeafBV hLeafBVSub).1,
          (st.tailAVAIL0).appendTERM1 (Term.var (supply.varAt st.availNext (hInv.available_vars st.availNext))))
  · exact (SearchTree.leaf leaf records, st)

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- Definition 5.4.9 (companion, preservation): `growRightAtLeaf`
    preserves `Inv`. Mirror of `growLeftAtLeaf_preserves_Inv`. -/
theorem growRightAtLeaf_preserves_Inv {L : Language} {supply : TermStream L} (hNoEq : L.hasEquality = false)
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq)
    (B : FormulaN L) (leaf : Sequent L)
    (st : SearchState L supply) (records : BranchRecords L) (hInv : SearchState.Inv seq bound st)
    (hLeafFV : LeafFVBelow supply leaf st.availNext)
    (hLeafBV : LeafBVBelow leaf bound)
    (hLeafBVSub : LeafBVSubsetSeq leaf seq) :
    SearchState.Inv seq bound
      (growRightAtLeaf hNoEq hNoFunc hCNFB B leaf st records hInv hLeafFV hLeafBV hLeafBVSub).2 := by
-- BEGIN PROOF
  classical
  unfold growRightAtLeaf
  by_cases hB : B ∈ leaf.succedent
  · simp only [hB, ↓reduceDIte]
    match B, hB with
    | .conj _ _, hB =>
        simp only [growRightOneProp_state_eq]; exact hInv
    | .disj _ _, hB =>
        simp only [growRightOneProp_state_eq]; exact hInv
    | .impl _ _, hB =>
        simp only [growRightOneProp_state_eq]; exact hInv
    | .neg _, hB =>
        simp only [growRightOneProp_state_eq]; exact hInv
    | .predN _ _, _ => simp only; exact hInv
    | .eq_ _ _ _, _ => simp only; exact hInv
    | .ex x C, hB =>
        simp only
        exact growRightExInv_preserves_Inv hNoFunc hCNFB x C leaf hB hLeafBVSub st records hInv
    | .all x C, hB =>
        simp only
        exact SearchState.Inv.tailAppend hInv
  · simp only [hB, ↓reduceDIte]; exact hInv

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- Definition 5.4.9 (companion, preservation): `growRightAtLeaf` leaves
    `availNext` ≥ its input (monotone). Mirror of
    `growLeftAtLeaf_availNext_mono`. -/
theorem growRightAtLeaf_availNext_mono {L : Language} {supply : TermStream L} (hNoEq : L.hasEquality = false)
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq)
    (B : FormulaN L) (leaf : Sequent L)
    (st : SearchState L supply) (records : BranchRecords L) (hInv : SearchState.Inv seq bound st)
    (hLeafFV : LeafFVBelow supply leaf st.availNext)
    (hLeafBV : LeafBVBelow leaf bound)
    (hLeafBVSub : LeafBVSubsetSeq leaf seq) :
    st.availNext ≤
      (growRightAtLeaf hNoEq hNoFunc hCNFB B leaf st records hInv hLeafFV hLeafBV hLeafBVSub).2.availNext := by
-- BEGIN PROOF
  classical
  unfold growRightAtLeaf
  by_cases hB : B ∈ leaf.succedent
  · simp only [hB, ↓reduceDIte]
    match B, hB with
    | .conj _ _, hB =>
        simp only [growRightOneProp_availNext_eq]; exact Nat.le_refl _
    | .disj _ _, hB =>
        simp only [growRightOneProp_availNext_eq]; exact Nat.le_refl _
    | .impl _ _, hB =>
        simp only [growRightOneProp_availNext_eq]; exact Nat.le_refl _
    | .neg _, hB =>
        simp only [growRightOneProp_availNext_eq]; exact Nat.le_refl _
    | .predN _ _, _ => exact Nat.le_refl _
    | .eq_ _ _ _, _ => exact Nat.le_refl _
    | .ex x C, hB =>
        simp only [growRightExInv_availNext_eq]; exact Nat.le_refl _
    | .all x C, hB =>
        exact Nat.le_succ _
  · simp only [hB, ↓reduceDIte]; exact Nat.le_refl _

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

/-- Definition 5.4.9 (companion, tree-level grow-right): Mirror of
    `growLeftTreeInv` for right rules. A universal principal formula uses
    one shared eigenvariable, activated once if a nonaxiom leaf is extended. -/
@[blueprint "chap5__definition_5_4_9"]
noncomputable def growRightTreeInv {L : Language} {supply : TermStream L} (hNoEq : L.hasEquality = false)
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq)
    (B : FormulaN L)
    {s : Sequent L} (t : SearchTree s) (st : SearchState L supply)
    (hInv : SearchState.Inv seq bound st)
    (hTLI : TreeLeafInv supply t seq st.availNext) :
    GrowOut supply (L := L) (s := s) seq bound st.availNext := by
  classical
  match B with
  | .all x body =>
      exact growEigenTree st hInv
        (fun leaf => FormulaN.all x body ∈ leaf.succedent)
        (fun leaf records hSel hFV hSub =>
          (growRightAtLeaf hNoEq hNoFunc hCNFB (FormulaN.all x body) leaf
            st records hInv hFV
            (LeafBVBelow_of_SubsetSeq hSub hInv.bound_above_seq) hSub).1)
        (by
          intro leaf records hSel hFV hSub
          have h := TreeLeafInv_grow_right_at_leaf hNoEq hNoFunc hCNFB
            (FormulaN.all x body) leaf st records hInv hFV
            (LeafBVBelow_of_SubsetSeq hSub hInv.bound_above_seq) hSub
          simpa only [growRightAtLeaf, dif_pos hSel,
            SearchState.appendTERM1, SearchState.tailAVAIL0] using h)
        t hTLI
  | _ =>
      let rec walk :
        {s : Sequent L} → (t : SearchTree s) → (st : SearchState L supply) →
        (hInv : SearchState.Inv seq bound st) →
        (hTLI : TreeLeafInv supply t seq st.availNext) →
        GrowOut supply (L := L) (s := s) seq bound st.availNext
      | _, .leaf l records, st, hInv, hTLI => by
          classical
          by_cases hAx : isAxiom l
          · exact
              { tree := SearchTree.leaf l records
                state := st
                state_inv := hInv
                avail_mono := Nat.le_refl _
                tree_leaf_inv := hTLI }
          · have hLeafIn : l ∈ (GDeductionTreeExt.leaf l).leaves := by
              simp [SearchTree.toDeductionTree, GDeductionTreeExt.leaves]
            obtain ⟨hFV, hSub⟩ := hTLI l hLeafIn
            let hBV : LeafBVBelow l bound :=
              LeafBVBelow_of_SubsetSeq hSub hInv.bound_above_seq
            let result := growRightAtLeaf hNoEq hNoFunc hCNFB B l st records hInv hFV hBV hSub
            exact
              { tree := result.1
                state := result.2
                state_inv := growRightAtLeaf_preserves_Inv hNoEq
                  hNoFunc hCNFB B l st records hInv hFV hBV hSub
                avail_mono := growRightAtLeaf_availNext_mono hNoEq
                  hNoFunc hCNFB B l st records hInv hFV hBV hSub
                tree_leaf_inv := TreeLeafInv_grow_right_at_leaf hNoEq
                  hNoFunc hCNFB B l st records hInv hFV hBV hSub }
      | _, .onePremise rule t, st, hInv, hTLI => by
          have hTLI' : TreeLeafInv supply t seq st.availNext := fun leaf hleaf =>
            hTLI leaf (by simp [SearchTree.toDeductionTree, GDeductionTreeExt.leaves]; exact hleaf)
          let out := walk t st hInv hTLI'
          exact
            { tree := SearchTree.onePremise rule out.tree
              state := out.state
              state_inv := out.state_inv
              avail_mono := out.avail_mono
              tree_leaf_inv := by
                intro leaf hleaf
                apply out.tree_leaf_inv leaf
                simp [SearchTree.toDeductionTree, GDeductionTreeExt.leaves] at hleaf
                exact hleaf }
      | _, .twoPremise rule t1 t2, st, hInv, hTLI => by
          have hTLI1 : TreeLeafInv supply t1 seq st.availNext := fun leaf hleaf =>
            hTLI leaf (by simp [SearchTree.toDeductionTree, GDeductionTreeExt.leaves]; left; exact hleaf)
          have hTLI2 : TreeLeafInv supply t2 seq st.availNext := fun leaf hleaf =>
            hTLI leaf (by simp [SearchTree.toDeductionTree, GDeductionTreeExt.leaves]; right; exact hleaf)
          let out1 := walk t1 st hInv hTLI1
          have hTLI2' : TreeLeafInv supply t2 seq out1.state.availNext :=
            TreeLeafInv_mono hTLI2 out1.avail_mono
          let out2 := walk t2 out1.state
                        out1.state_inv hTLI2'
          exact
            { tree := SearchTree.twoPremise rule out1.tree out2.tree
              state := out2.state
              state_inv := out2.state_inv
              avail_mono := Nat.le_trans out1.avail_mono out2.avail_mono
              tree_leaf_inv := by
                intro leaf hleaf
                simp [SearchTree.toDeductionTree, GDeductionTreeExt.leaves] at hleaf
                rcases hleaf with h1 | h2
                · have h := out1.tree_leaf_inv leaf h1
                  exact ⟨LeafFVBelow_mono h.1 out2.avail_mono, h.2⟩
                · exact out2.tree_leaf_inv leaf h2 }
      exact walk t st hInv hTLI

/-- Mirror for grow-right. -/
@[blueprint "chap5__definition_5_4_9"]
noncomputable def foldGrowRight {L : Language} {supply : TermStream L} (hNoEq : L.hasEquality = false)
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq) :
    List (FormulaN L) →
    {s : Sequent L} → (t : SearchTree s) → (st : SearchState L supply) →
    (hInv : SearchState.Inv seq bound st) →
    (hTLI : TreeLeafInv supply t seq st.availNext) →
    GrowOut supply (L := L) (s := s) seq bound st.availNext
  | [], _, t, st, hInv, hTLI =>
      { tree := t, state := st, state_inv := hInv
        avail_mono := Nat.le_refl _, tree_leaf_inv := hTLI }
  | B :: Bs, _, t, st, hInv, hTLI => by
      let out1 := growRightTreeInv hNoEq hNoFunc hCNFB B t st hInv hTLI
      have hTLI2 : TreeLeafInv supply out1.tree seq out1.state.availNext :=
        out1.tree_leaf_inv
      let out2 := foldGrowRight hNoEq hNoFunc hCNFB Bs out1.tree out1.state
                    out1.state_inv hTLI2
      exact
        { tree := out2.tree, state := out2.state
          state_inv := out2.state_inv
          avail_mono := Nat.le_trans out1.avail_mono out2.avail_mono
          tree_leaf_inv := out2.tree_leaf_inv }

end LCS.FirstOrder.Gentzen.Search.NoFunction
end
