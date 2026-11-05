import LCS.Item
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.Hintikka
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics.Subformulae
import LCS.FirstOrder.Gentzen.Search.NoFunction.Initialization
import Attach
import LCS.FirstOrder.Gentzen.Search.NoFunction.Growth.ProofsStamp

section
namespace LCS.FirstOrder.Gentzen.Search.NoFunction
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.4.9 (required helper): Classical extraction of the
    split witness from `list_split_mem`. Uses `Classical.choose` — pure
    existential extraction, not a search-procedure oracle. Returned as a
    `Σ`-shaped record so that downstream `let ⟨Γ, Δ, hsplit⟩ := ...`
    destructuring works. -/
noncomputable def splitListAt {α : Type} (l : List α) (a : α) (h : a ∈ l) :
    { p : List α × List α // l = p.1 ++ [a] ++ p.2 } :=
  let pre := (list_split_mem l a h).choose
  let post := (list_split_mem l a h).choose_spec.choose
  ⟨(pre, post), (list_split_mem l a h).choose_spec.choose_spec⟩

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


-- ===================================================================
-- Leaf-level variable bound: every FV in a leaf sequent is < availNext
-- ===================================================================

/-- Definition 5.4.9 (companion): No free variable of the leaf occurs
    at or after the given position in the availability enumeration. -/
@[blueprint "chap5__definition_5_4_9"]
def LeafFVBelow {L : Language} (supply : TermStream L) (leaf : Sequent L) (bound : Nat) : Prop :=
  ∀ F ∈ leaf.antecedent ++ leaf.succedent,
    ∀ j ∈ formulaFVN F, BeforeCursor supply bound j

/-- Definition 5.4.9 (companion, leaf-level invariant): Every BOUND
    variable occurring in any formula of a leaf sequent has index
    strictly less than a given `bound`. Dual of `LeafFVBelow` for the
    BV side. The bound is the static `bound` parameter of `Inv`; rule applications don't introduce new binders, so BV
    indices stay bounded by the original `bound` forever. -/
@[blueprint "chap5__definition_5_4_9"]
def LeafBVBelow {L : Language} (leaf : Sequent L) (bound : Nat) : Prop :=
  ∀ F ∈ leaf.antecedent ++ leaf.succedent,
    ∀ j ∈ formulaBVN F, j < bound

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- Definition 5.4.9 (companion): Advancing the availability cursor
    preserves freshness for a leaf. -/
theorem LeafFVBelow_mono {L : Language} {supply : TermStream L} {leaf : Sequent L} {b b' : Nat}
    (h : LeafFVBelow supply leaf b) (hle : b ≤ b') : LeafFVBelow supply leaf b' := by
-- BEGIN PROOF
  intro F hF j hj
  exact (h F hF j hj).mono hle



-- ===================================================================
-- Subformula / BV-subset invariant (§5.4.9 tree-level preservation)
-- ===================================================================

/-- Definition 5.4.9 (companion, tree-level invariant): Every binder
    occurring in any formula of `leaf` already occurs as a binder in
    some formula of the original sequent `seq`. Formally:

      ∀ F ∈ leaf, ∀ y ∈ BV(F), ∃ G ∈ seq, y ∈ BV(G).

    This is the textbook's implicit invariant ("no rule introduces new
    binders" — every Gentzen rule either decomposes a formula into
    subformulas or substitutes a term for a free variable, both
    operations PRESERVE the set of binders). Preserved under all
    twelve rule applications of `GentzenStep1Ext`/`GentzenStep2Ext`.

    Used to discharge `y ∉ BV(F)` for free-for substitution at deeper
    leaves: combined with `Inv seq bound st` + `crossNoFreeBound seq`,
    gives `y ∉ BV(G)` for every `G ∈ seq`, then the BV-subset lifts
    to `y ∉ BV(F)` for every `F ∈ leaf`. -/
@[blueprint "chap5__definition_5_4_9"]
def LeafBVSubsetSeq {L : Language} (leaf seq : Sequent L) : Prop :=
  ∀ F ∈ leaf.antecedent ++ leaf.succedent,
    ∀ y ∈ formulaBVN F,
      ∃ G ∈ seq.antecedent ++ seq.succedent, y ∈ formulaBVN G

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Definition 5.4.9 (companion, tree-level invariant): Reflexivity —
    a sequent trivially has its own BVs as a subset of its own BVs. -/
theorem LeafBVSubsetSeq.refl {L : Language} (seq : Sequent L) :
    LeafBVSubsetSeq seq seq := by
-- BEGIN PROOF
  intro F hF y hy
  exact ⟨F, hF, hy⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 5.4.9 (companion, discharge): If `LeafBVSubsetSeq leaf seq`
    and `i ∉ BV(G)` for every `G ∈ seq`, then `i ∉ BV(F)` for every
    `F ∈ leaf`. This is how the leaf-level free-for discharge descends
    from the `seq`-level `crossNoFreeBound` / `NoVarAbove` witnesses. -/
theorem notBV_leaf_of_notBV_seq {L : Language} {leaf seq : Sequent L}
    (hSub : LeafBVSubsetSeq leaf seq) {i : Nat}
    (hNotBV : ∀ G ∈ seq.antecedent ++ seq.succedent, i ∉ formulaBVN G)
    (F : FormulaN L) (hF : F ∈ leaf.antecedent ++ leaf.succedent) :
    i ∉ formulaBVN F := by
-- BEGIN PROOF
  intro hiBV
  obtain ⟨G, hG, hiG⟩ := hSub F hF i hiBV
  exact hNotBV G hG hiG

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.LeafInvariant
/-- Definition 5.4.9 (required helper): `formulaBVN (formulaSubstN A t x)
    ⊆ formulaBVN A`. Term substitution cannot introduce new binders
    because `Term L` has no quantifier constructor — terms only
    contribute free variables. Proved by induction on `A`. -/
theorem formulaBVN_formulaSubstN_subset {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat) :
    formulaBVN (formulaSubstN A t x) ⊆ formulaBVN A := by
-- BEGIN PROOF
  intro y hy
  induction A with
  | predN _ _ => exact hy
  | eq_ _ _ _ => exact hy
  | neg A ih =>
    show y ∈ formulaBVN A
    exact ih hy
  | conj A B ihA ihB =>
    show y ∈ formulaBVN A ∪ formulaBVN B
    rcases hy with hyA | hyB
    · exact Or.inl (ihA hyA)
    · exact Or.inr (ihB hyB)
  | disj A B ihA ihB =>
    show y ∈ formulaBVN A ∪ formulaBVN B
    rcases hy with hyA | hyB
    · exact Or.inl (ihA hyA)
    · exact Or.inr (ihB hyB)
  | impl A B ihA ihB =>
    show y ∈ formulaBVN A ∪ formulaBVN B
    rcases hy with hyA | hyB
    · exact Or.inl (ihA hyA)
    · exact Or.inr (ihB hyB)
  | all z A ih =>
    -- formulaSubstN (.all z A) t x = if x ≠ z then .all z (formulaSubstN A t x) else .all z A
    show y ∈ formulaBVN A ∪ Set.singleton z
    unfold formulaSubstN at hy
    split at hy
    · -- x ≠ z case: formulaSubstN = .all z (formulaSubstN A t x)
      -- BV = formulaBVN (formulaSubstN A t x) ∪ {z}
      rcases hy with hyA | hyZ
      · exact Or.inl (ih hyA)
      · exact Or.inr hyZ
    · -- x = z case: formulaSubstN = .all z A, so BV = formulaBVN A ∪ {z}
      exact hy
  | ex z A ih =>
    show y ∈ formulaBVN A ∪ Set.singleton z
    unfold formulaSubstN at hy
    split at hy
    · rcases hy with hyA | hyZ
      · exact Or.inl (ih hyA)
      · exact Or.inr hyZ
    · exact hy

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- Definition 5.4.9 (companion, leaf-level invariant): `LeafBVBelow`
    for `leaf` follows from `LeafBVSubsetSeq leaf seq` +
    `NoVarAbove seq bound`. Every BV-index in `leaf` is in some BV of
    `seq`, which is `< bound` by `NoVarAbove`. -/
theorem LeafBVBelow_of_SubsetSeq {L : Language} {leaf seq : Sequent L}
    (hSub : LeafBVSubsetSeq leaf seq) {bound : Nat}
    (hNVA : NoVarAbove seq bound) :
    LeafBVBelow leaf bound := by
-- BEGIN PROOF
  intro F hF j hj
  obtain ⟨G, hG, hjG⟩ := hSub F hF j hj
  exact (hNVA G hG).2 j hjG

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
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

-- ===================================================================
-- Tree walker: extendAllNonaxiomLeaves (§5.4.9 "extend every nonaxiom leaf")
-- ===================================================================







-- ===================================================================
-- Tree-level leaf invariants (packaged for walker consumption)
-- ===================================================================

/-- Definition 5.4.9 (companion): Every leaf is fresh for the unconsumed
    availability stream, and its bound variables occur among the input's
    bound variables. Leaf annotations do not affect these conditions. -/
@[blueprint "chap5__definition_5_4_9"]
def TreeLeafInv {L : Language} (supply : TermStream L) {s : Sequent L}
    (t : SearchTree s) (seq : Sequent L) (bound : Nat) : Prop :=
  ∀ leaf ∈ t.toDeductionTree.leaves,
    LeafFVBelow supply leaf bound ∧
    LeafBVSubsetSeq leaf seq

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- Definition 5.4.9 (companion, tree invariant): `TreeLeafInv` is
    monotone in `bound` — if FV below `b`, then also below any `b' ≥ b`. -/
theorem TreeLeafInv_mono {L : Language} {supply : TermStream L} {s : Sequent L}
    {t : SearchTree s} {seq : Sequent L} {b b' : Nat}
    (h : TreeLeafInv supply t seq b) (hle : b ≤ b') : TreeLeafInv supply t seq b' := by
-- BEGIN PROOF
  intro leaf hleaf
  obtain ⟨hFV, hSub⟩ := h leaf hleaf
  exact ⟨LeafFVBelow_mono hFV hle, hSub⟩

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- Definition 5.4.9 (companion): A one-leaf search tree satisfies the
    invariant when the supplied availability tail is fresh for its sequent. -/
theorem TreeLeafInv_init {L : Language} {supply : TermStream L} (seq : Sequent L) (bound : Nat) (records : BranchRecords L)
    (hFresh : LeafFVBelow supply seq bound) :
    TreeLeafInv supply (SearchTree.leaf seq records) seq bound := by
-- BEGIN PROOF
  intro leaf hleaf
  simp [SearchTree.toDeductionTree, GDeductionTreeExt.leaves] at hleaf
  refine ⟨?_, ?_⟩
  · intro F hF j hj
    rw [hleaf] at hF
    exact hFresh F hF j hj
  · rw [hleaf]
    exact LeafBVSubsetSeq.refl seq

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- Definition 5.4.9 (companion, tree invariant): `TreeLeafInv` on
    `onePremise rule t` reduces to `TreeLeafInv` on `t`, since
    `leaves (onePremise _ t) = leaves t`. -/
theorem TreeLeafInv_onePremise {L : Language} {supply : TermStream L} {prem conc : Sequent L}
    (rule : GentzenStep1Ext prem conc) (t : SearchTree prem)
    {seq : Sequent L} {bound : Nat} :
    TreeLeafInv supply (SearchTree.onePremise rule t) seq bound ↔
      TreeLeafInv supply t seq bound := by
-- BEGIN PROOF
  constructor <;> intro h leaf hleaf
  · exact h leaf (by simp [SearchTree.toDeductionTree, GDeductionTreeExt.leaves]; exact hleaf)
  · apply h leaf
    simp [SearchTree.toDeductionTree, GDeductionTreeExt.leaves] at hleaf
    exact hleaf

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- Definition 5.4.9 (companion, tree invariant): `TreeLeafInv` on
    `twoPremise rule t1 t2` reduces to conjunction on `t1` and `t2`. -/
theorem TreeLeafInv_twoPremise {L : Language} {supply : TermStream L} {p1 p2 conc : Sequent L}
    (rule : GentzenStep2Ext p1 p2 conc) (t1 : SearchTree p1)
    (t2 : SearchTree p2)
    {seq : Sequent L} {bound : Nat} :
    TreeLeafInv supply (SearchTree.twoPremise rule t1 t2) seq bound ↔
      TreeLeafInv supply t1 seq bound ∧ TreeLeafInv supply t2 seq bound := by
-- BEGIN PROOF
  constructor
  · intro h
    refine ⟨fun leaf hleaf => ?_, fun leaf hleaf => ?_⟩
    · apply h leaf; simp [SearchTree.toDeductionTree, GDeductionTreeExt.leaves]; left; exact hleaf
    · apply h leaf; simp [SearchTree.toDeductionTree, GDeductionTreeExt.leaves]; right; exact hleaf
  · rintro ⟨h1, h2⟩ leaf hleaf
    simp [SearchTree.toDeductionTree, GDeductionTreeExt.leaves] at hleaf
    rcases hleaf with h_in1 | h_in2
    · exact h1 leaf h_in1
    · exact h2 leaf h_in2

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
/-- `growRightOneProp` leaves `SearchState` unchanged. -/
theorem growRightOneProp_state_eq {L : Language} {supply : TermStream L} (B : FormulaN L)
    (leaf : Sequent L) (hB : B ∈ leaf.succedent) (st : SearchState L supply) (records : BranchRecords L) :
    (growRightOneProp B leaf hB st records).2 = st := by
-- BEGIN PROOF
  unfold growRightOneProp; split <;> rfl

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Advancing AVAIL₀ and appending its former head to TERM₁ preserves
    the state invariant. Stream injectivity excludes that variable from
    every later position. -/
theorem SearchState.Inv.tailAppend {L : Language} {supply : TermStream L}
    {seq : Sequent L} {bound : Nat} {st : SearchState L supply}
    (h : SearchState.Inv seq bound st) :
    SearchState.Inv seq bound
      ((st.tailAVAIL0).appendTERM1 (Term.var (supply.varAt st.availNext (h.available_vars st.availNext)))) := by
  apply SearchState.appendTERM1_preserves_Inv (SearchState.tailAVAIL0_preserves_Inv h)
  · intro i hi
    have hEq := Term.var.inj hi
    right
    exact hEq ▸ h.avail_fresh st.availNext (Nat.le_refl _) _
      (supply.varAt_spec st.availNext (h.available_vars st.availNext))
  · intro i hi
    have hEq := Term.var.inj hi
    exact hEq ▸ supply.varAt_beforeSucc st.availNext (h.available_vars st.availNext)

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
/-- `growRightOneProp` doesn't touch `availNext`. -/
theorem growRightOneProp_availNext_eq {L : Language} {supply : TermStream L} (B : FormulaN L)
    (leaf : Sequent L) (hB : B ∈ leaf.succedent) (st : SearchState L supply) (records : BranchRecords L) :
    (growRightOneProp B leaf hB st records).2.availNext = st.availNext := by
-- BEGIN PROOF
  rw [growRightOneProp_state_eq]

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

-- ===================================================================
-- Per-leaf preservation of TreeLeafInv (PROVED — porting from worktree)
-- ===================================================================

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.LeafInvariant
/-- Definition 5.4.9 (required helper): Casting a deduction tree's
    index doesn't change its leaves (they're a polymorphic
    `List (Sequent L)`, not dependent on the type index). Used in
    preservation proofs to strip the `hConc ▸` transport wrapper
    produced by the propositional grow-* primitives. -/
theorem leaves_cast {L : Language} {s1 s2 : Sequent L} (heq : s1 = s2)
    (t : SearchTree s1) : (heq ▸ t).toDeductionTree.leaves = t.toDeductionTree.leaves := by
-- BEGIN PROOF
  subst heq
  rfl

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.LeafInvariant
/-- Every variable of an activated term is absent from the unconsumed
    availability stream. Function terms are excluded by the language hypothesis. -/
theorem termFV_of_tTERM0_lt_availNext {L : Language} {supply : TermStream L}
    (hNoFunc : L.funSymbols → False)
    {seq : Sequent L} {bound : Nat} {st : SearchState L supply}
    (h : SearchState.Inv seq bound st)
    {t : Term L} (ht : t ∈ st.tTERM0) :
    ∀ j ∈ termFV t, BeforeCursor supply st.availNext j := by
-- BEGIN PROOF
  unfold SearchState.tTERM0 at ht
  intro j hj
  match t with
  | .var i =>
    have hji : j = i := hj
    subst hji
    exact h.terms_below_avail _ ht j rfl
  | .const c => exact absurd hj id
  | .func f _ => exact (hNoFunc f).elim





-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.LeafInvariant
/-- Definition 5.4.9 (required helper): `leaf.antecedent ++ leaf.succedent`
    membership splits through list append. -/
theorem mem_antSucc_of_mem_antecedent {L : Language}
    {leaf : Sequent L} {F : FormulaN L} (h : F ∈ leaf.antecedent) :
    F ∈ leaf.antecedent ++ leaf.succedent :=
-- BEGIN PROOF
  List.mem_append.mpr (Or.inl h)

-- retained: used by LCS.FirstOrder.Gentzen.Search.NoFunction.LeafInvariant
theorem mem_antSucc_of_mem_succedent {L : Language}
    {leaf : Sequent L} {F : FormulaN L} (h : F ∈ leaf.succedent) :
    F ∈ leaf.antecedent ++ leaf.succedent :=
-- BEGIN PROOF
  List.mem_append.mpr (Or.inr h)



end LCS.FirstOrder.Gentzen.Search.NoFunction
end

