import LCS.Item
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.Hintikka
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics.Subformulae
import LCS.FirstOrder.Gentzen.Search.NoFunction.LeafExtension
import Attach
import LCS.FirstOrder.Gentzen.Search.NoFunction.GrowLeft.ProofsStamp

/-! # Procedure grow-left (Definition 5.4.9)

The left rules applied at a leaf (propositional connectives, for-all:left with the
terms of TERM₀, exists:left with head(AVAIL₀)), their effect on the search state,
and grow-left on every nonaxiom leaf of a tree.
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

-- ===================================================================
-- growLeftOne / growRightOne: propositional cases
-- ===================================================================

/-- Definition 5.4.9 (companion, `grow-left` propositional cases):
    Given a principal antecedent formula `A` occurring in a single
    leaf sequent `leaf`, build the subtree produced by applying the
    G-rule whose principal formula on the left is `A`. Returns the
    extended subtree (whose conclusion is `leaf`) together with the
    updated search state.

    Textbook §5.4.9 (grow-left procedure) enumerates the cases by
    `A`'s main connective:
    - `A = B ∧ C`  : one-premise ∧:left rule.
    - `A = B ∨ C`  : two-premise ∨:left rule.
    - `A = B ⊃ C`  : two-premise ⊃:left rule.
    - `A = ¬B`     : one-premise ¬:left rule.
    - `A = ∀x B` / `A = ∃x B`  : quantifier cases (handled in
      `growLeftOneQuant` below — they consume AVAIL₀ / iterate
      TERM₀ so their shape is different from propositional cases).
    - `A` atomic (`predN` / `eq_`) : no rule applies, return
      `(.leaf leaf, st)` unchanged.

    This function dispatches only on the PROPOSITIONAL cases plus the
    atomic no-op; quantifier cases are handled by `growLeftOneQuant`. -/
@[blueprint "chap5__definition_5_4_9"]
noncomputable def growLeftOneProp {L : Language} {supply : TermStream L}
    (A : FormulaN L) (leaf : Sequent L)
    (hA : A ∈ leaf.antecedent) (st : SearchState L supply) (records : BranchRecords L) :
    SearchTree leaf × SearchState L supply :=
  match hAcase : A with
  | .conj B C =>
      have hAin : FormulaN.conj B C ∈ leaf.antecedent := hAcase ▸ hA
      let split := splitListAt leaf.antecedent (FormulaN.conj B C) hAin
      let Γ := split.val.1
      let Δ := split.val.2
      let conc : Sequent L := Sequent.mk (Γ ++ [FormulaN.conj B C] ++ Δ) leaf.succedent
      let prem : Sequent L := Sequent.mk (Γ ++ [B, C] ++ Δ) leaf.succedent
      let rule : GentzenStep1Ext prem conc := GentzenStep1Ext.conjLeft Γ Δ leaf.succedent B C
      let t' : SearchTree conc :=
        SearchTree.onePremise rule (SearchTree.leaf prem records)
      have hConc : conc = leaf := by
        show Sequent.mk _ _ = leaf
        congr 1
        exact split.property.symm
      (hConc ▸ t', st)
  | .disj B C =>
      have hAin : FormulaN.disj B C ∈ leaf.antecedent := hAcase ▸ hA
      let split := splitListAt leaf.antecedent (FormulaN.disj B C) hAin
      let Γ := split.val.1
      let Δ := split.val.2
      let conc : Sequent L := Sequent.mk (Γ ++ [FormulaN.disj B C] ++ Δ) leaf.succedent
      let premL : Sequent L := Sequent.mk (Γ ++ [B] ++ Δ) leaf.succedent
      let premR : Sequent L := Sequent.mk (Γ ++ [C] ++ Δ) leaf.succedent
      let rule : GentzenStep2Ext premL premR conc :=
        GentzenStep2Ext.disjLeft Γ Δ leaf.succedent B C
      let t' : SearchTree conc :=
        SearchTree.twoPremise rule
          (SearchTree.leaf premL records) (SearchTree.leaf premR records)
      have hConc : conc = leaf := by
        show Sequent.mk _ _ = leaf
        congr 1
        exact split.property.symm
      (hConc ▸ t', st)
  | .impl B C =>
      have hAin : FormulaN.impl B C ∈ leaf.antecedent := hAcase ▸ hA
      let split := splitListAt leaf.antecedent (FormulaN.impl B C) hAin
      let Γ := split.val.1
      let Δ := split.val.2
      let conc : Sequent L := Sequent.mk (Γ ++ [FormulaN.impl B C] ++ Δ) leaf.succedent
      let premL : Sequent L := Sequent.mk (Γ ++ Δ) ([B] ++ leaf.succedent)
      let premR : Sequent L := Sequent.mk ([C] ++ Γ ++ Δ) leaf.succedent
      let rule : GentzenStep2Ext premL premR conc :=
        GentzenStep2Ext.implLeft Γ Δ leaf.succedent B C
      let t' : SearchTree conc :=
        SearchTree.twoPremise rule
          (SearchTree.leaf premL records) (SearchTree.leaf premR records)
      have hConc : conc = leaf := by
        show Sequent.mk _ _ = leaf
        congr 1
        exact split.property.symm
      (hConc ▸ t', st)
  | .neg B =>
      have hAin : FormulaN.neg B ∈ leaf.antecedent := hAcase ▸ hA
      let split := splitListAt leaf.antecedent (FormulaN.neg B) hAin
      let Γ := split.val.1
      let Δ := split.val.2
      let conc : Sequent L := Sequent.mk (Γ ++ [FormulaN.neg B] ++ Δ) leaf.succedent
      let prem : Sequent L := Sequent.mk (Γ ++ Δ) ([B] ++ leaf.succedent)
      let rule : GentzenStep1Ext prem conc := GentzenStep1Ext.negLeft Γ Δ leaf.succedent B
      let t' : SearchTree conc :=
        SearchTree.onePremise rule (SearchTree.leaf prem records)
      have hConc : conc = leaf := by
        show Sequent.mk _ _ = leaf
        congr 1
        exact split.property.symm
      (hConc ▸ t', st)
  -- atomic / quantifier / `eq_` cases: no propositional rule applies.
  -- Return the trivial one-leaf tree at `leaf` — no transport needed.
  | .predN _ _ => (SearchTree.leaf leaf records, st)
  | .eq_ _ _ _ => (SearchTree.leaf leaf records, st)
  | .all _ _ => (SearchTree.leaf leaf records, st)
  | .ex _ _ => (SearchTree.leaf leaf records, st)

/-- Definition 5.4.9 (companion, discharge — leaf-level): Every term
    `u ∈ tTERM0 st` is free for substitution for `y` in a formula `A`
    that occurs as the body of a `∀z A` at some leaf formula,
    provided the usual §5.4.7 standing assumptions PLUS
    `LeafBVSubsetSeq leaf seq`.

    This is the tree-walker-compatible replacement for
    `term_isFreeForN_body_all_of_Inv`: instead of `hInSeq : ∀z A ∈ seq`,
    we take `hInLeaf : ∀z A ∈ leaf` and lift BV-nonmembership from
    `seq` to `leaf` via the subformula invariant. -/
theorem SearchState.term_isFreeForN_body_all_of_Inv_Sub {L : Language} {supply : TermStream L}
    (hNoFunc : L.funSymbols → False)
    {seq leaf : Sequent L} {bound : Nat} {st : SearchState L supply}
    (h : SearchState.Inv seq bound st)
    (hCNFB : crossNoFreeBound seq)
    (hSub : LeafBVSubsetSeq leaf seq)
    {u : Term L} (hu : u ∈ st.tTERM0)
    (z : Nat) (A : FormulaN L)
    (hInLeaf : FormulaN.all z A ∈ leaf.antecedent ++ leaf.succedent) :
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
    have hNotBV_all : i ∉ formulaBVN (FormulaN.all z A) :=
      notBV_leaf_of_notBV_seq hSub hNotBVSeq _ hInLeaf
    have hNotBV_A : i ∉ formulaBVN A := notBV_body_of_all hNotBV_all
    exact isFreeForN_var_of_notBV i y A hNotBV_A
  | .const c => exact isFreeForN_const c y A
  | .func f _ => exact (hNoFunc f).elim

-- ===================================================================
-- Quantifier-aware grow-left / grow-right (∀x A / ∃x A / ∃x C / ∀x C)
-- ===================================================================

/-- Definition 5.4.9 (companion, `grow-left` ∀x A case, invariant-aware):
    Apply the §5.4.8 extended ∀:left rule at a leaf whose antecedent
    contains `∀x A`. The list of terms `ts` is computed internally by
    filtering `tTERM0 st` against this branch's FORM₀; `hne` and
    `hfree` are discharged from the state invariant and §5.4.7
    standing assumptions:

    - `hNoFunc`   — no function symbols in `L` (§5.4.7 standing)
    - `hInv`      — `Inv seq bound st` (the variable-bookkeeping state invariant)
    - `hCNFB`     — `crossNoFreeBound seq` (§5.4.7 standing assumption)
    - `hLeafBVSub` — `LeafBVSubsetSeq leaf seq`: every binder in `leaf`
                     already occurs as a binder in `seq`. Preserved across
                     rule applications (no rule introduces new binders).

    The child leaf inherits the branch records with the principal formula
    appended to FORM₁ for every selected term. FORM₀ and the global state
    are unchanged by this step.

    Textbook §5.4.9 grow-left (∀x B case, lines 147-154):
    "for every term u_k ∈ t(TERM₀) such that A is not in FORM₀(k) do
     extend every nonaxiom leaf of S by applying the ∀ : left rule
     using the term u_k as one of the terms of the rule.
     In TERM₁ let FORM₁(k) := append(FORM₁(k), A)".

    When the filtered list is empty (all available terms already
    saturated with this principal formula), the rule does NOT fire —
    the textbook's "for every ... such that ..." loop is empty, so the
    subtree is unchanged. -/
@[blueprint "chap5__definition_5_4_9"]
noncomputable def growLeftAllInv {L : Language} {supply : TermStream L}
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq)
    (x : Nat) (A : FormulaN L) (leaf : Sequent L)
    (hA : FormulaN.all x A ∈ leaf.antecedent)
    (hLeafBVSub : LeafBVSubsetSeq leaf seq)
    (st : SearchState L supply) (records : BranchRecords L)
    (hInv : SearchState.Inv seq bound st) :
    SearchTree leaf × SearchState L supply := by
  classical
  let indexedTerms : List (Term L × Nat) :=
    st.tTERM0.mapIdx (fun k t => (t, k))
  let filtered : List (Term L × Nat) :=
    indexedTerms.filter (fun p => ¬ SearchState.isUsed records p.2 (FormulaN.all x A))
  let ts : List (Term L) := filtered.map Prod.fst
  let ks : List Nat := filtered.map Prod.snd
  by_cases hEmpty : ts = []
  · exact (SearchTree.leaf leaf records, st)
  · have hne : ts ≠ [] := hEmpty
    have hAllInLeafList :
        FormulaN.all x A ∈ leaf.antecedent ++ leaf.succedent :=
      List.mem_append.mpr (Or.inl hA)
    have hfree : ∀ t ∈ ts, isFreeForN t x A := by
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
      exact SearchState.term_isFreeForN_body_all_of_Inv_Sub
              hNoFunc hInv hCNFB hLeafBVSub hInTTERM0 x A hAllInLeafList x
    let split := splitListAt leaf.antecedent (FormulaN.all x A) hA
    let Γ := split.val.1
    let Δ := split.val.2
    let Λ := leaf.succedent
    let conc : Sequent L := Sequent.mk (Γ ++ [FormulaN.all x A] ++ Δ) Λ
    let prem : Sequent L :=
      Sequent.mk
        (Γ ++ ts.map (fun t => formulaSubstN A t x) ++ [FormulaN.all x A] ++ Δ) Λ
    let rule : GentzenStep1Ext prem conc :=
      GentzenStep1Ext.allLeft ts Γ Δ Λ x A hne hfree
    let records' : BranchRecords L :=
      ks.foldl (fun r k => SearchState.appendFORM1 r k (FormulaN.all x A)) records
    let t' : SearchTree conc :=
      SearchTree.onePremise rule (SearchTree.leaf prem records')
    have hConc : conc = leaf := by
      show Sequent.mk _ _ = leaf
      congr 1
      exact split.property.symm
    exact (hConc ▸ t', st)

/-- Definition 5.4.9 (companion, `grow-left` ∃x A case, invariant-aware):
    Apply the ∃:left rule at a leaf whose antecedent contains `∃x A`.
    The global state is returned unchanged; the tree-level caller activates
    the shared eigenvariable after extending all eligible leaves.
    The eigenvariable `y` is the variable at the current AVAIL₀ cursor
    (textbook §5.4.9 line 159); its `hfresh` and `hfreeFor` side
    conditions are discharged from the state invariant and the
    leaf-level FV bound.

    Hypotheses:
    - `hInv`      — `Inv seq bound st`
    - `hLeafFV`   — `LeafFVBelow leaf st.availNext`: every free
                    variable in any formula of `leaf` has index
                    `< availNext`. Maintained inductively by the outer
                    tree walker.
    - `hLeafBV`   — `LeafBVBelow leaf bound`: every bound variable in
                    any formula of `leaf` has index `< bound`.
                    Preserved across rule applications (no rule
                    introduces new binders).
    - `hA`        — `∃x A ∈ leaf.antecedent`

    Textbook §5.4.9 grow-left (∃x B case, lines 157-162):
    "extend every nonaxiom leaf of S by applying the ∃ : left rule
     using y = head(AVAIL₀) as the new variable;
     TERM₁ := append(TERM₁, ⟨y, nil⟩);
     AVAIL₀ := tail(AVAIL₀)".

    `head(AVAIL₀)` is always defined because `AVAIL₀` is the
    countably-infinite stream `⟨y_{availNext}, y_{availNext+1}, …⟩` —
    no exhaustion case. -/
@[blueprint "chap5__definition_5_4_9"]
noncomputable def growLeftExInv {L : Language} {supply : TermStream L}
    {seq : Sequent L} {bound : Nat}
    (x : Nat) (A : FormulaN L) (leaf : Sequent L)
    (hA : FormulaN.ex x A ∈ leaf.antecedent)
    (st : SearchState L supply) (records : BranchRecords L) (hInv : SearchState.Inv seq bound st)
    (hLeafFV : LeafFVBelow supply leaf st.availNext)
    (hLeafBV : LeafBVBelow leaf bound)
    (hLeafBVSub : LeafBVSubsetSeq leaf seq) :
    SearchTree leaf × SearchState L supply := by
  let y : Nat := supply.varAt st.availNext (hInv.available_vars st.availNext)
  have hy : supply.entries st.availNext = some (.var y) :=
    supply.varAt_spec st.availNext (hInv.available_vars st.availNext)
  let split := splitListAt leaf.antecedent (FormulaN.ex x A) hA
  let Γ := split.val.1
  let Δ := split.val.2
  let Λ := leaf.succedent
  -- hfresh: for every F in the CONCLUSION sequent (= leaf),
  -- y = availNext ∉ FV(F) because LeafFVBelow supply says FV(F) < availNext.
  have hfresh :
      ∀ F ∈ (Sequent.mk (Γ ++ [FormulaN.ex x A] ++ Δ) Λ).antecedent ++
            (Sequent.mk (Γ ++ [FormulaN.ex x A] ++ Δ) Λ).succedent,
        y ∉ formulaFVN F := by
    intro F hF
    have hFInLeaf : F ∈ leaf.antecedent ++ leaf.succedent := by
      rcases List.mem_append.mp hF with hAnt | hSucc
      · have hEq : Γ ++ [FormulaN.ex x A] ++ Δ = leaf.antecedent :=
          split.property.symm
        exact List.mem_append.mpr (Or.inl (hEq ▸ hAnt))
      · exact List.mem_append.mpr (Or.inr hSucc)
    intro hYin
    exact hLeafFV F hFInLeaf y hYin st.availNext (Nat.le_refl _) hy
  -- The availability invariant and inherited binder set give capture-freeness.
  have hExInLeafList :
      FormulaN.ex x A ∈ leaf.antecedent ++ leaf.succedent := by
    simp only [List.mem_append]; left; exact hA
  have hYnotBV_A : y ∉ formulaBVN A :=
    notBV_body_of_ex (notBV_leaf_of_notBV_seq hLeafBVSub
      (hInv.avail_fresh st.availNext (Nat.le_refl _) y hy) _ hExInLeafList)
  have hfreeFor : isFreeForN (Term.var y) x A :=
    isFreeForN_var_of_notBV y x A hYnotBV_A
  let conc : Sequent L := Sequent.mk (Γ ++ [FormulaN.ex x A] ++ Δ) Λ
  let prem : Sequent L :=
    Sequent.mk (Γ ++ [formulaSubstN A (Term.var y) x] ++ Δ) Λ
  let rule : GentzenStep1Ext prem conc :=
    GentzenStep1Ext.exLeft y Γ Δ Λ x A hfresh hfreeFor
  let t' : SearchTree conc :=
    SearchTree.onePremise rule (SearchTree.leaf prem records)
  have hConc : conc = leaf := by
    show Sequent.mk _ _ = leaf
    congr 1
    exact split.property.symm
  exact (hConc ▸ t', st)

-- ===================================================================
-- Inv preservation for per-leaf grow-* primitives
-- ===================================================================

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- `growLeftOneProp` leaves `SearchState` unchanged. -/
theorem growLeftOneProp_state_eq {L : Language} {supply : TermStream L} (A : FormulaN L)
    (leaf : Sequent L) (hA : A ∈ leaf.antecedent) (st : SearchState L supply) (records : BranchRecords L) :
    (growLeftOneProp A leaf hA st records).2 = st := by
-- BEGIN PROOF
  unfold growLeftOneProp; split <;> rfl

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- Definition 5.4.9 (companion, preservation): `growLeftAllInv`
    preserves `Inv`: the operation changes only branch records and
    leaves the global state unchanged. -/
theorem growLeftAllInv_preserves_Inv {L : Language} {supply : TermStream L}
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq)
    (x : Nat) (A : FormulaN L) (leaf : Sequent L)
    (hA : FormulaN.all x A ∈ leaf.antecedent)
    (hLeafBVSub : LeafBVSubsetSeq leaf seq)
    (st : SearchState L supply) (records : BranchRecords L) (hInv : SearchState.Inv seq bound st) :
    SearchState.Inv seq bound
      (growLeftAllInv hNoFunc hCNFB x A leaf hA hLeafBVSub st records hInv).2 := by
  classical
  unfold growLeftAllInv
  dsimp only
  split <;> exact hInv

-- ===================================================================
-- availNext identities for per-leaf grow-*
-- ===================================================================

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- `growLeftOneProp` doesn't touch `availNext`. -/
theorem growLeftOneProp_availNext_eq {L : Language} {supply : TermStream L} (A : FormulaN L)
    (leaf : Sequent L) (hA : A ∈ leaf.antecedent) (st : SearchState L supply) (records : BranchRecords L) :
    (growLeftOneProp A leaf hA st records).2.availNext = st.availNext := by
-- BEGIN PROOF
  rw [growLeftOneProp_state_eq]

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- `growLeftAllInv` leaves the global state, and hence `availNext`, unchanged. -/
theorem growLeftAllInv_availNext_eq {L : Language} {supply : TermStream L}
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq)
    (x : Nat) (A : FormulaN L) (leaf : Sequent L)
    (hA : FormulaN.all x A ∈ leaf.antecedent)
    (hLeafBVSub : LeafBVSubsetSeq leaf seq)
    (st : SearchState L supply) (records : BranchRecords L) (hInv : SearchState.Inv seq bound st) :
    (growLeftAllInv hNoFunc hCNFB x A leaf hA hLeafBVSub st records hInv).2.availNext
      = st.availNext := by
  classical
  unfold growLeftAllInv
  dsimp only
  split <;> rfl

-- ===================================================================
-- Per-leaf grow-left / grow-right dispatchers
-- ===================================================================

/-- Definition 5.4.9 (companion, `grow-left` at a leaf): Dispatch on
    principal antecedent formula `A`'s main connective and apply the
    matching grow-* primitive. If `A ∉ leaf.antecedent` or `A` is atomic,
    return the leaf unchanged. All leaf-level invariants needed by the
    quantifier-case primitives are supplied by the caller.

    Noncomputable because it classically decides `A ∈ leaf.antecedent`
    (FormulaN's DecidableEq is classical). -/
@[blueprint "chap5__definition_5_4_9"]
noncomputable def growLeftAtLeaf {L : Language} {supply : TermStream L} (hNoEq : L.hasEquality = false)
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq)
    (A : FormulaN L) (leaf : Sequent L)
    (st : SearchState L supply) (records : BranchRecords L) (hInv : SearchState.Inv seq bound st)
    (hLeafFV : LeafFVBelow supply leaf st.availNext)
    (hLeafBV : LeafBVBelow leaf bound)
    (hLeafBVSub : LeafBVSubsetSeq leaf seq) :
    SearchTree leaf × SearchState L supply := by
  classical
  by_cases hA : A ∈ leaf.antecedent
  · match A, hA with
    | .conj _ _, hA => exact growLeftOneProp _ leaf hA st records
    | .disj _ _, hA => exact growLeftOneProp _ leaf hA st records
    | .impl _ _, hA => exact growLeftOneProp _ leaf hA st records
    | .neg _, hA => exact growLeftOneProp _ leaf hA st records
    | .predN _ _, _ => exact (SearchTree.leaf leaf records, st)
    | .eq_ _ _ _, _ => exact (SearchTree.leaf leaf records, st)
    | .all x B, hA =>
        exact growLeftAllInv hNoFunc hCNFB x B leaf hA hLeafBVSub st records hInv
    | .ex x B, hA =>
        exact ((growLeftExInv x B leaf hA st records hInv hLeafFV hLeafBV hLeafBVSub).1,
          (st.tailAVAIL0).appendTERM1 (Term.var (supply.varAt st.availNext (hInv.available_vars st.availNext))))
  · exact (SearchTree.leaf leaf records, st)

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- Definition 5.4.9 (companion, preservation): `growLeftAtLeaf`
    preserves `Inv`. Case analysis over `A`'s constructor plus per-case
    preservation lemmas. -/
theorem growLeftAtLeaf_preserves_Inv {L : Language} {supply : TermStream L} (hNoEq : L.hasEquality = false)
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq)
    (A : FormulaN L) (leaf : Sequent L)
    (st : SearchState L supply) (records : BranchRecords L) (hInv : SearchState.Inv seq bound st)
    (hLeafFV : LeafFVBelow supply leaf st.availNext)
    (hLeafBV : LeafBVBelow leaf bound)
    (hLeafBVSub : LeafBVSubsetSeq leaf seq) :
    SearchState.Inv seq bound
      (growLeftAtLeaf hNoEq hNoFunc hCNFB A leaf st records hInv hLeafFV hLeafBV hLeafBVSub).2 := by
-- BEGIN PROOF
  classical
  unfold growLeftAtLeaf
  by_cases hA : A ∈ leaf.antecedent
  · simp only [hA, ↓reduceDIte]
    match A, hA with
    | .conj _ _, hA =>
        simp only; rw [growLeftOneProp_state_eq]; exact hInv
    | .disj _ _, hA =>
        simp only; rw [growLeftOneProp_state_eq]; exact hInv
    | .impl _ _, hA =>
        simp only; rw [growLeftOneProp_state_eq]; exact hInv
    | .neg _, hA =>
        simp only; rw [growLeftOneProp_state_eq]; exact hInv
    | .predN _ _, _ => simp only; exact hInv
    | .eq_ _ _ _, _ => simp only; exact hInv
    | .all x B, hA =>
        simp only
        exact growLeftAllInv_preserves_Inv hNoFunc hCNFB x B leaf hA hLeafBVSub st records hInv
    | .ex x B, hA =>
        simp only
        exact SearchState.Inv.tailAppend hInv
  · simp only [hA, ↓reduceDIte]; exact hInv

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- Definition 5.4.9 (companion, preservation): `growLeftAtLeaf` leaves
    `availNext` ≥ its input (monotone). -/
theorem growLeftAtLeaf_availNext_mono {L : Language} {supply : TermStream L} (hNoEq : L.hasEquality = false)
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq)
    (A : FormulaN L) (leaf : Sequent L)
    (st : SearchState L supply) (records : BranchRecords L) (hInv : SearchState.Inv seq bound st)
    (hLeafFV : LeafFVBelow supply leaf st.availNext)
    (hLeafBV : LeafBVBelow leaf bound)
    (hLeafBVSub : LeafBVSubsetSeq leaf seq) :
    st.availNext ≤
      (growLeftAtLeaf hNoEq hNoFunc hCNFB A leaf st records hInv hLeafFV hLeafBV hLeafBVSub).2.availNext := by
-- BEGIN PROOF
  classical
  unfold growLeftAtLeaf
  by_cases hA : A ∈ leaf.antecedent
  · simp only [hA, ↓reduceDIte]
    match A, hA with
    | .conj _ _, hA =>
        simp only [growLeftOneProp_availNext_eq]; exact Nat.le_refl _
    | .disj _ _, hA =>
        simp only [growLeftOneProp_availNext_eq]; exact Nat.le_refl _
    | .impl _ _, hA =>
        simp only [growLeftOneProp_availNext_eq]; exact Nat.le_refl _
    | .neg _, hA =>
        simp only [growLeftOneProp_availNext_eq]; exact Nat.le_refl _
    | .predN _ _, _ => exact Nat.le_refl _
    | .eq_ _ _ _, _ => exact Nat.le_refl _
    | .all x B, hA =>
        simp only [growLeftAllInv_availNext_eq]; exact Nat.le_refl _
    | .ex x B, hA =>
        exact Nat.le_succ _
  · simp only [hA, ↓reduceDIte]; exact Nat.le_refl _

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

/-- Definition 5.4.9 (companion, tree-level grow-left): Apply
    `growLeftAtLeaf` to every non-axiom leaf of a tree `t`. At each
    leaf visit, per-leaf invariants are extracted from the tree-level
    `TreeLeafInv`. Axiom leaves are preserved unchanged. State is
    threaded through the walk in leaves-order, matching the §5.4.9
    textbook pseudocode ("extend every nonaxiom leaf of S").

    Returns a bundled `GrowOut` carrying: the new tree, the threaded
    state, `Inv` preservation, `availNext` monotonicity, and
    `TreeLeafInv` preservation at the new `availNext`. The last
    invariant relies on `TreeLeafInv_grow_at_leaf` (proved via case
    analysis over 8 formula constructors using `formulaFVN_formulaSubstN`
    and `formulaBVN_formulaSubstN_subset`).

    For an existential principal formula, all selected leaves use the
    same input head of AVAIL₀, and the global state is updated once when
    at least one nonaxiom leaf is extended. Other connectives thread
    the global state through the recursive walk. -/
@[blueprint "chap5__definition_5_4_9"]
noncomputable def growLeftTreeInv {L : Language} {supply : TermStream L} (hNoEq : L.hasEquality = false)
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat}
    (hCNFB : crossNoFreeBound seq)
    (A : FormulaN L)
    {s : Sequent L} (t : SearchTree s) (st : SearchState L supply)
    (hInv : SearchState.Inv seq bound st)
    (hTLI : TreeLeafInv supply t seq st.availNext) :
    GrowOut supply (L := L) (s := s) seq bound st.availNext := by
  classical
  match A with
  | .ex x body =>
      exact growEigenTree st hInv
        (fun leaf => FormulaN.ex x body ∈ leaf.antecedent)
        (fun leaf records hSel hFV hSub =>
          (growLeftAtLeaf hNoEq hNoFunc hCNFB (FormulaN.ex x body) leaf
            st records hInv hFV
            (LeafBVBelow_of_SubsetSeq hSub hInv.bound_above_seq) hSub).1)
        (by
          intro leaf records hSel hFV hSub
          have h := TreeLeafInv_grow_at_leaf hNoEq hNoFunc hCNFB
            (FormulaN.ex x body) leaf st records hInv hFV
            (LeafBVBelow_of_SubsetSeq hSub hInv.bound_above_seq) hSub
          simpa only [growLeftAtLeaf, dif_pos hSel,
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
            let result := growLeftAtLeaf hNoEq hNoFunc hCNFB A l st records hInv hFV hBV hSub
            exact
              { tree := result.1
                state := result.2
                state_inv := growLeftAtLeaf_preserves_Inv hNoEq
                  hNoFunc hCNFB A l st records hInv hFV hBV hSub
                avail_mono := growLeftAtLeaf_availNext_mono hNoEq
                  hNoFunc hCNFB A l st records hInv hFV hBV hSub
                tree_leaf_inv := TreeLeafInv_grow_at_leaf hNoEq
                  hNoFunc hCNFB A l st records hInv hFV hBV hSub }
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

-- ===================================================================
-- expand: per-leaf grow-left / grow-right (§5.4.9 lines 111-131)
-- ===================================================================

/-- Helper: fold `growLeftTreeInv` over a list of principal formulas,
    threading state and tree across iterations. -/
@[blueprint "chap5__definition_5_4_9"]
noncomputable def foldGrowLeft {L : Language} {supply : TermStream L} (hNoEq : L.hasEquality = false)
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
  | A :: As, _, t, st, hInv, hTLI => by
      let out1 := growLeftTreeInv hNoEq hNoFunc hCNFB A t st hInv hTLI
      have hTLI2 : TreeLeafInv supply out1.tree seq out1.state.availNext :=
        out1.tree_leaf_inv
      let out2 := foldGrowLeft hNoEq hNoFunc hCNFB As out1.tree out1.state
                    out1.state_inv hTLI2
      exact
        { tree := out2.tree, state := out2.state
          state_inv := out2.state_inv
          avail_mono := Nat.le_trans out1.avail_mono out2.avail_mono
          tree_leaf_inv := out2.tree_leaf_inv }

end LCS.FirstOrder.Gentzen.Search.NoFunction
end
