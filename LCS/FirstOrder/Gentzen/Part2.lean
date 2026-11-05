import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.SyntaxN
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics
import LCS.FirstOrder.SemanticsN
import LCS.FirstOrder.SemanticsN.Substitution
import LCS.FirstOrder.Gentzen.Part1
import Attach
import LCS.FirstOrder.Gentzen.Part2.ProofsStamp

section
namespace LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution

-- retained: used by LCS.FirstOrder.Equality.Part2
/-- Lemma 5.4.2 (companion): `sequentValid seq ↔ ∀ M, ¬ sequentFalsifiableIn M seq`. -/
theorem sequentValid_iff_not_falsifiable {L : Language} (seq : Sequent L) :
    sequentValid seq ↔ ∀ M : Structure L, ¬ sequentFalsifiableIn M seq := by
-- BEGIN PROOF
  constructor
  · intro h M ⟨s, hant, hsucc⟩
    obtain ⟨B, hBmem, hBeval⟩ := h M s hant
    exact hsucc B hBmem hBeval
  · intro h M s hant
    apply Classical.byContradiction
    intro hcontra
    apply h M
    refine ⟨s, hant, fun B hB hEval => hcontra ⟨B, hB, hEval⟩⟩

/-- Definition 5.4.2 (companion): A sequent over a language without equality
is valid iff it is not falsifiable in any structure. -/
@[blueprint "chap5__definition_5_4_2"]
theorem sequentValid_iff_not_falsifiableNoEq {L : Language} (hL : L.withoutEquality)
    (seq : SequentNoEq L hL) :
    sequentValidNoEq hL seq ↔ ∀ M : Structure L, ¬ sequentFalsifiableInNoEq hL M seq 

-- retained: used by LCS.CutElim.LK.Part1
/-- Lemma 5.4.2 (companion): For each one-premise rule of G over a language
without equality, the conclusion sequent is valid iff the premise is valid. -/
theorem ruleValidityIff1 {L : Language} (hL : L.withoutEquality)
    {prem conc : Sequent L} (rule : GentzenStep1 hL prem conc) :
    sequentValid conc ↔ sequentValid prem := by
-- BEGIN PROOF
  rw [sequentValid_iff_not_falsifiable, sequentValid_iff_not_falsifiable]
  exact forall_congr' (fun M => not_congr (ruleFalsificationIff1 hL M rule))

-- retained: used by LCS.CutElim.LK.Part1
/-- Lemma 5.4.2 (companion): For each two-premise rule of G over a language
without equality, the conclusion sequent is valid iff both premises are valid. -/
theorem ruleValidityIff2 {L : Language} (hL : L.withoutEquality)
    {prem1 prem2 conc : Sequent L} (rule : GentzenStep2 hL prem1 prem2 conc) :
    sequentValid conc ↔ (sequentValid prem1 ∧ sequentValid prem2) := by
-- BEGIN PROOF
  rw [sequentValid_iff_not_falsifiable, sequentValid_iff_not_falsifiable,
      sequentValid_iff_not_falsifiable]
  constructor
  · intro h
    refine ⟨fun M hF => h M ?_, fun M hF => h M ?_⟩
    · exact (ruleFalsificationIff2 hL M rule).mpr (Or.inl hF)
    · exact (ruleFalsificationIff2 hL M rule).mpr (Or.inr hF)
  · intro ⟨h1, h2⟩ M hF
    rcases (ruleFalsificationIff2 hL M rule).mp hF with hF1 | hF2
    · exact h1 M hF1
    · exact h2 M hF2

-- ===================================================================
-- Lemma 5.4.3: Soundness of G
-- ===================================================================

-- retained: used by LCS.CutElim.LK.Part1
/-- Lemma 5.4.3 (companion): Every indexed proof tree in G over a language
without equality has a valid conclusion sequent. Proved by induction on the tree, using
`ruleValidityIff1`/`ruleValidityIff2` for the inductive steps. -/
theorem proofTreeValid {L : Language} (hL : L.withoutEquality) {s : Sequent L}
    (t : GProofTree hL s) : sequentValid s := by
-- BEGIN PROOF
  induction t with
  | axiom_ s hax =>
    intro M as hant
    obtain ⟨A, hA_ant, hA_suc⟩ := hax
    exact ⟨A, hA_suc, hant A hA_ant⟩
  | onePremise rule _ ih =>
    exact (ruleValidityIff1 hL rule).mpr ih
  | twoPremise rule _ _ ih1 ih2 =>
    exact (ruleValidityIff2 hL rule).mpr ⟨ih1, ih2⟩

/-- Lemma 5.4.3: Soundness of G over a language without equality. If a
sequent is provable (there exists an indexed GProofTree with that conclusion), then the sequent is valid. -/
@[blueprint "chap5__lemma_5_4_3" (main := true)]
theorem soundnessG {L : Language} (hL : L.withoutEquality) (seq : Sequent L)
    (h : sequentProvable hL seq) : sequentValid seq 

-- ===================================================================
-- Definition 5.4.8: Extended Gentzen system G (k-term ∀:left / ∃:right)
-- ===================================================================

/-- Definition 5.6.2 (companion): One-premise G rules inside G_=, for any
    equality flag. The ∀:left and ∃:right rules use the §5.4.8 extended schema:
    a nonempty list of terms, each free for the substituted variable, gives
    the corresponding list of substitution instances in the premise. -/
@[blueprint "chap5__definition_5_6_2"]
inductive GentzenStep1Ext {L : Language} : Sequent L → Sequent L → Type where
  | conjLeft (Γ Δ Λ : List (FormulaN L)) (A B : FormulaN L) :
      GentzenStep1Ext (Sequent.mk (Γ ++ [A, B] ++ Δ) Λ)
                       (Sequent.mk (Γ ++ [FormulaN.conj A B] ++ Δ) Λ)
  | disjRight (Γ Δ Λ : List (FormulaN L)) (A B : FormulaN L) :
      GentzenStep1Ext (Sequent.mk Γ (Δ ++ [A, B] ++ Λ))
                       (Sequent.mk Γ (Δ ++ [FormulaN.disj A B] ++ Λ))
  | implRight (Γ Δ Λ : List (FormulaN L)) (A B : FormulaN L) :
      GentzenStep1Ext (Sequent.mk ([A] ++ Γ) ([B] ++ Δ ++ Λ))
                       (Sequent.mk Γ (Δ ++ [FormulaN.impl A B] ++ Λ))
  | negLeft (Γ Δ Λ : List (FormulaN L)) (A : FormulaN L) :
      GentzenStep1Ext (Sequent.mk (Γ ++ Δ) ([A] ++ Λ))
                       (Sequent.mk (Γ ++ [FormulaN.neg A] ++ Δ) Λ)
  | negRight (Γ Δ Λ : List (FormulaN L)) (A : FormulaN L) :
      GentzenStep1Ext (Sequent.mk ([A] ++ Γ) (Δ ++ Λ))
                       (Sequent.mk Γ (Δ ++ [FormulaN.neg A] ++ Λ))
  /-- Extended ∀:left from Definition 5.4.8, taking a nonempty list of
      k terms (k ≥ 1), each free for x in A. -/
  | allLeft (ts : List (Term L)) (Γ Δ Λ : List (FormulaN L))
      (x : Nat) (A : FormulaN L) (hne : ts ≠ [])
      (hfree : ∀ t ∈ ts, isFreeForN t x A) :
      GentzenStep1Ext
        (Sequent.mk
          (Γ ++ ts.map (fun t => formulaSubstN A t x) ++ [FormulaN.all x A] ++ Δ)
          Λ)
        (Sequent.mk (Γ ++ [FormulaN.all x A] ++ Δ) Λ)
  | allRight (y : Nat) (Γ Δ Λ : List (FormulaN L))
      (x : Nat) (A : FormulaN L)
      (hfresh : ∀ F ∈ (Sequent.mk Γ (Δ ++ [FormulaN.all x A] ++ Λ)).antecedent ++
        (Sequent.mk Γ (Δ ++ [FormulaN.all x A] ++ Λ)).succedent,
        y ∉ formulaFVN F)
      (hfreeFor : isFreeForN (Term.var y) x A) :
      GentzenStep1Ext
        (Sequent.mk Γ
          (Δ ++ [formulaSubstN A (Term.var y) x] ++ Λ))
        (Sequent.mk Γ (Δ ++ [FormulaN.all x A] ++ Λ))
  | exLeft (y : Nat) (Γ Δ Λ : List (FormulaN L))
      (x : Nat) (A : FormulaN L)
      (hfresh : ∀ F ∈ (Sequent.mk (Γ ++ [FormulaN.ex x A] ++ Δ) Λ).antecedent ++
        (Sequent.mk (Γ ++ [FormulaN.ex x A] ++ Δ) Λ).succedent,
        y ∉ formulaFVN F)
      (hfreeFor : isFreeForN (Term.var y) x A) :
      GentzenStep1Ext
        (Sequent.mk
          (Γ ++ [formulaSubstN A (Term.var y) x] ++ Δ) Λ)
        (Sequent.mk (Γ ++ [FormulaN.ex x A] ++ Δ) Λ)
  /-- Extended ∃:right from Definition 5.4.8, taking a nonempty list of
      k terms (k ≥ 1), each free for x in A. -/
  | exRight (ts : List (Term L)) (Γ Δ Λ : List (FormulaN L))
      (x : Nat) (A : FormulaN L) (hne : ts ≠ [])
      (hfree : ∀ t ∈ ts, isFreeForN t x A) :
      GentzenStep1Ext
        (Sequent.mk Γ
          (Δ ++ ts.map (fun t => formulaSubstN A t x) ++ [FormulaN.ex x A] ++ Λ))
        (Sequent.mk Γ (Δ ++ [FormulaN.ex x A] ++ Λ))

/-- Definition 5.6.2 (companion): Two-premise G rules inside G_=, for any
    equality flag. These propositional rules are shared by the single-term
    and §5.4.8 extended systems. -/
@[blueprint "chap5__definition_5_6_2"]
inductive GentzenStep2Ext {L : Language} :
    Sequent L → Sequent L → Sequent L → Type where
  | conjRight (Γ Δ Λ : List (FormulaN L)) (A B : FormulaN L) :
      GentzenStep2Ext (Sequent.mk Γ (Δ ++ [A] ++ Λ))
                      (Sequent.mk Γ (Δ ++ [B] ++ Λ))
                      (Sequent.mk Γ (Δ ++ [FormulaN.conj A B] ++ Λ))
  | disjLeft (Γ Δ Λ : List (FormulaN L)) (A B : FormulaN L) :
      GentzenStep2Ext (Sequent.mk (Γ ++ [A] ++ Δ) Λ)
                      (Sequent.mk (Γ ++ [B] ++ Δ) Λ)
                      (Sequent.mk (Γ ++ [FormulaN.disj A B] ++ Δ) Λ)
  | implLeft (Γ Δ Λ : List (FormulaN L)) (A B : FormulaN L) :
      GentzenStep2Ext (Sequent.mk (Γ ++ Δ) ([A] ++ Λ))
                      (Sequent.mk ([B] ++ Γ ++ Δ) Λ)
                      (Sequent.mk (Γ ++ [FormulaN.impl A B] ++ Δ) Λ)

/-- Definition 5.6.2 (companion): Proof trees for the G rules inside G_=,
    for any equality flag, indexed by conclusion sequent. Leaves are axiom
    sequents; inference nodes use `GentzenStep1Ext` and `GentzenStep2Ext`
    under the §5.4.8 extended-rule convention. -/
@[blueprint "chap5__definition_5_6_2"]
inductive GProofTreeExt {L : Language} : Sequent L → Type where
  | axiom_ (s : Sequent L) (h : isAxiom s) : GProofTreeExt s
  | onePremise {prem conc : Sequent L}
      (rule : GentzenStep1Ext prem conc)
      (t : GProofTreeExt prem) : GProofTreeExt conc
  | twoPremise {prem1 prem2 conc : Sequent L}
      (rule : GentzenStep2Ext prem1 prem2 conc)
      (t1 : GProofTreeExt prem1) (t2 : GProofTreeExt prem2) :
      GProofTreeExt conc

/-- Definition 5.6.2 (companion): Deduction trees for the G rules inside G_=,
    for any equality flag, indexed by conclusion sequent. Leaves are arbitrary
    sequents; inference nodes use `GentzenStep1Ext` and `GentzenStep2Ext`
    under the §5.4.8 extended-rule convention. -/
@[blueprint "chap5__definition_5_6_2"]
inductive GDeductionTreeExt {L : Language} : Sequent L → Type where
  | leaf (s : Sequent L) : GDeductionTreeExt s
  | onePremise {prem conc : Sequent L}
      (rule : GentzenStep1Ext prem conc)
      (t : GDeductionTreeExt prem) : GDeductionTreeExt conc
  | twoPremise {p1 p2 conc : Sequent L}
      (rule : GentzenStep2Ext p1 p2 conc)
      (t1 : GDeductionTreeExt p1) (t2 : GDeductionTreeExt p2) :
      GDeductionTreeExt conc

end LCS.FirstOrder.Gentzen
end

section
namespace LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution
namespace GDeductionTreeExt

/-- Definition 5.6.2 (companion): The conclusion of an indexed extended
    deduction tree is its type index (same as for `GProofTreeExt`). -/
@[blueprint "chap5__definition_5_6_2"]
def conclusion {L : Language} {s : Sequent L} (_ : GDeductionTreeExt s) : Sequent L := s

-- retained: used by LCS.CutElim.LK.Part1.Proofs
@[simp]
theorem conclusion_eq {L : Language} {s : Sequent L}
    (t : GDeductionTreeExt s) : t.conclusion = s := rfl

/-- Definition 5.6.2 (companion): A deduction tree is a proof tree iff
    all its leaves are axiom sequents. This general form applies for any equality flag. -/
@[blueprint "chap5__definition_5_6_2"]
def isProof {L : Language} : {s : Sequent L} → GDeductionTreeExt s → Prop
  | _, .leaf s => isAxiom s
  | _, .onePremise _ t => t.isProof
  | _, .twoPremise _ t1 t2 => t1.isProof ∧ t2.isProof

/-- Definition 5.6.2 (companion): Converts an extended deduction tree
    whose leaves are all axioms into a `GProofTreeExt` of the same
    conclusion. -/
@[blueprint "chap5__definition_5_6_2"]
def toProofTree {L : Language} :
    {s : Sequent L} → (t : GDeductionTreeExt s) → t.isProof → GProofTreeExt s
  | _, .leaf s, hax => GProofTreeExt.axiom_ s hax
  | _, .onePremise rule t, hp => GProofTreeExt.onePremise rule (t.toProofTree hp)
  | _, .twoPremise rule t1 t2, hp =>
      GProofTreeExt.twoPremise rule
        (t1.toProofTree hp.1) (t2.toProofTree hp.2)

/-- Definition 5.6.2 (companion): Collects all leaf sequents of an
    extended deduction tree. Textbook Def 5.4.2 refers back to Def 3.4.5
    for the tree structure; the notion of leaf is inherited. -/
@[blueprint "chap5__definition_5_6_2"]
def leaves {L : Language} :
    {s : Sequent L} → GDeductionTreeExt s → List (Sequent L)
  | _, .leaf s => [s]
  | _, .onePremise _ t => t.leaves
  | _, .twoPremise _ t1 t2 => t1.leaves ++ t2.leaves

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp]
theorem leaves_leaf {L : Language} (s : Sequent L) :
    (GDeductionTreeExt.leaf s).leaves = [s] := rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp]
theorem leaves_onePremise {L : Language} {prem conc : Sequent L}
    (rule : GentzenStep1Ext prem conc) (t : GDeductionTreeExt prem) :
    (GDeductionTreeExt.onePremise rule t).leaves = t.leaves := rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
@[simp]
theorem leaves_twoPremise {L : Language} {p1 p2 conc : Sequent L}
    (rule : GentzenStep2Ext p1 p2 conc)
    (t1 : GDeductionTreeExt p1) (t2 : GDeductionTreeExt p2) :
    (GDeductionTreeExt.twoPremise rule t1 t2).leaves = t1.leaves ++ t2.leaves := rfl

/-- Definition 5.6.2 (companion): An extended deduction tree is closed
    iff every leaf sequent is an axiom. A pure property of the tree
    (independent of any search procedure): coincides with `isProof`
    (see `isProof_iff_isClosed` below). -/
@[blueprint "chap5__definition_5_6_2"]
def isClosed {L : Language} {s : Sequent L}
    (t : GDeductionTreeExt s) : Prop :=
  ∀ l ∈ t.leaves, isAxiom l



-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- An extended deduction tree is a proof
    tree (`isProof`) iff it is closed (all leaves are axioms). The two
    predicates agree definitionally on each constructor. -/
theorem isProof_iff_isClosed {L : Language} :
    {s : Sequent L} → (t : GDeductionTreeExt s) → t.isProof ↔ t.isClosed
  | _, .leaf s => by
      constructor
      · intro h l hl
        simp [leaves] at hl
        subst hl
        exact h
      · intro h
        apply h
        simp [leaves]
  | _, .onePremise _ t => by
      have ih := isProof_iff_isClosed t
      show GDeductionTreeExt.isProof t ↔ _
      unfold isClosed leaves
      exact ih
  | _, .twoPremise _ t1 t2 => by
      have ih1 := isProof_iff_isClosed t1
      have ih2 := isProof_iff_isClosed t2
      show GDeductionTreeExt.isProof t1 ∧ GDeductionTreeExt.isProof t2 ↔ _
      unfold isClosed leaves
      unfold isClosed at ih1 ih2
      constructor
      · intro h l hl
        simp [List.mem_append] at hl
        cases hl with
        | inl h1 => exact ih1.mp h.1 l h1
        | inr h2 => exact ih2.mp h.2 l h2
      · intro h
        refine ⟨ih1.mpr ?_, ih2.mpr ?_⟩
        · intro l hl
          apply h
          simp [List.mem_append]; left; exact hl
        · intro l hl
          apply h
          simp [List.mem_append]; right; exact hl

end GDeductionTreeExt
end LCS.FirstOrder.Gentzen
end

section
namespace LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution

/-- Definition 5.6.2 (companion): Provability using the G rules inside G_=,
    for any equality flag, means existence of a `GProofTreeExt` with the given
    conclusion, under the §5.4.8 extended-rule convention. -/
@[blueprint "chap5__definition_5_6_2"]
def sequentProvableExt {L : Language} (s : Sequent L) : Prop :=
  Nonempty (GProofTreeExt s)

/-- Definition 5.4.1 (companion): One-premise G rules over a language without
    equality, using the §5.4.8 extended quantifier rules. -/
@[blueprint "chap5__definition_5_4_8"]
abbrev GentzenStep1ExtNoEq {L : Language} (hL : L.withoutEquality) :=
  @GentzenStep1Ext L

/-- Definition 5.4.1 (companion): Two-premise G rules over a language without
    equality, under the §5.4.8 standing assumption. -/
@[blueprint "chap5__definition_5_4_8"]
abbrev GentzenStep2ExtNoEq {L : Language} (hL : L.withoutEquality) :=
  @GentzenStep2Ext L

/-- Definition 5.4.2 (companion): G proof trees over a language without
    equality, using the §5.4.8 extended quantifier rules. -/
@[blueprint "chap5__definition_5_4_8"]
abbrev GProofTreeExtNoEq {L : Language} (hL : L.withoutEquality) :=
  @GProofTreeExt L

/-- Definition 5.4.2 (companion): G deduction trees over a language without
    equality, using the §5.4.8 extended quantifier rules. -/
@[blueprint "chap5__definition_5_4_8"]
abbrev GDeductionTreeExtNoEq {L : Language} (hL : L.withoutEquality) :=
  @GDeductionTreeExt L

/-- Definition 5.4.2 (companion): G provability over a language without
    equality, using the §5.4.8 extended quantifier rules. -/
@[blueprint "chap5__definition_5_4_8"]
def sequentProvableExtNoEq {L : Language} (hL : L.withoutEquality)
    (s : SequentNoEq L hL) : Prop :=
  sequentProvableExt s

-- ===================================================================
-- Definition 5.4.8 — the two extended quantifier rule schemas
-- ===================================================================

/-- Definition 5.4.8: The extended ∀:left rule schema.

    Textbook Def 5.4.8:
        Γ, A[t₁/x], …, A[tₖ/x], ∀x A, Δ → Λ
        ─────────────────────────────────────  (∀:left)
              Γ, ∀x A, Δ → Λ
    where t₁,…,tₖ are any k terms (k ≥ 1) free for x in A.

    The schema also applies inside G_= (Definition 5.6.2) and is
    equivalent to the `GentzenStep1Ext.allLeft` constructor. -/
@[blueprint "chap5__definition_5_6_2"]
inductive ExtendedAllLeft {L : Language} : Sequent L → Sequent L → Type where
  | mk (ts : List (Term L)) (Γ Δ Λ : List (FormulaN L))
       (x : Nat) (A : FormulaN L)
       (hne : ts ≠ [])
       (hfree : ∀ t ∈ ts, isFreeForN t x A) :
      ExtendedAllLeft
        (Sequent.mk
          (Γ ++ ts.map (fun t => formulaSubstN A t x) ++ [FormulaN.all x A] ++ Δ) Λ)
        (Sequent.mk (Γ ++ [FormulaN.all x A] ++ Δ) Λ)

/-- Definition 5.4.8: The extended ∃:right rule schema.

    Textbook Def 5.4.8:
        Γ → Δ, A[t₁/x], …, A[tₖ/x], ∃x A, Λ
        ─────────────────────────────────────  (∃:right)
              Γ → Δ, ∃x A, Λ
    where t₁,…,tₖ are any k terms (k ≥ 1) free for x in A.

    The schema also applies inside G_= (Definition 5.6.2) and is
    equivalent to the `GentzenStep1Ext.exRight` constructor. -/
@[blueprint "chap5__definition_5_6_2"]
inductive ExtendedExRight {L : Language} : Sequent L → Sequent L → Type where
  | mk (ts : List (Term L)) (Γ Δ Λ : List (FormulaN L))
       (x : Nat) (A : FormulaN L)
       (hne : ts ≠ [])
       (hfree : ∀ t ∈ ts, isFreeForN t x A) :
      ExtendedExRight
        (Sequent.mk Γ
          (Δ ++ ts.map (fun t => formulaSubstN A t x) ++ [FormulaN.ex x A] ++ Λ))
        (Sequent.mk Γ (Δ ++ [FormulaN.ex x A] ++ Λ))

/-- Definition 5.4.8: The extended ∀:left schema over a language without equality. -/
@[blueprint "chap5__definition_5_4_8" (main := true)]
abbrev ExtendedAllLeftNoEq {L : Language} (hL : L.withoutEquality)
    (prem conc : Sequent L) : Type :=
  ExtendedAllLeft prem conc

/-- Definition 5.4.8: The extended ∃:right schema over a language without equality. -/
@[blueprint "chap5__definition_5_4_8" (main := true)]
abbrev ExtendedExRightNoEq {L : Language} (hL : L.withoutEquality)
    (prem conc : Sequent L) : Type :=
  ExtendedExRight prem conc

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The standalone schema is inhabited exactly when the corresponding
constructor of `GentzenStep1Ext` connects the same premise and conclusion. -/
theorem ExtendedAllLeft.iff_gentzenStep1Ext {L : Language} (prem conc : Sequent L) :
    Nonempty (ExtendedAllLeft prem conc) ↔
      ∃ step : GentzenStep1Ext prem conc,
        (match step with
        | .allLeft _ _ _ _ _ _ _ _ => True
        | _ => False) := by
  constructor
  · rintro ⟨step⟩
    cases step with
    | mk ts Γ Δ Λ x A hne hfree =>
      exact ⟨.allLeft ts Γ Δ Λ x A hne hfree, True.intro⟩
  · rintro ⟨step, h⟩
    cases step with
    | allLeft ts Γ Δ Λ x A hne hfree =>
      exact ⟨.mk ts Γ Δ Λ x A hne hfree⟩
    | _ => exact False.elim h

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The standalone schema is inhabited exactly when the corresponding
constructor of `GentzenStep1Ext` connects the same premise and conclusion. -/
theorem ExtendedExRight.iff_gentzenStep1Ext {L : Language} (prem conc : Sequent L) :
    Nonempty (ExtendedExRight prem conc) ↔
      ∃ step : GentzenStep1Ext prem conc,
        (match step with
        | .exRight _ _ _ _ _ _ _ _ => True
        | _ => False) := by
  constructor
  · rintro ⟨step⟩
    cases step with
    | mk ts Γ Δ Λ x A hne hfree =>
      exact ⟨.exRight ts Γ Δ Λ x A hne hfree, True.intro⟩
  · rintro ⟨step, h⟩
    cases step with
    | exRight ts Γ Δ Λ x A hne hfree =>
      exact ⟨.mk ts Γ Δ Λ x A hne hfree⟩
    | _ => exact False.elim h

-- ===================================================================
-- Simulation theorems linking the Def-5.4.8 extended rules to Def 5.4.1
-- ===================================================================

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Simulation theorem (substantive direction): Over a language without
    equality, every k-term extended G-proof can be simulated by k applications of the original
    single-term G-rule, yielding a single-term G-proof of the same
    conclusion. Textbook §5.4.8: "an inference using this new version
    of the ∀:left rule (resp. ∃:right rule) can be simulated by k
    applications of the old ∀:left rule (resp. ∃:right rule). Hence,
    there is no gain of generality." This justifies treating the
    §5.4.8 extended rules as the G rules from that point onwards,
    since every extended G-proof corresponds to a standard G-proof of
    the same sequent. -/
noncomputable def GProofTreeExt.simulateBySingleTerm {L : Language} (hL : L.withoutEquality)
    {s : Sequent L} (t : GProofTreeExt s) : GProofTree hL s := by
-- BEGIN PROOF
  -- DEBT(§5.4.8: simulation of a k-term inference by k single-term applications; OD-10)
  sorry



-- ===================================================================
-- Lemma 5.4.2: Falsification/validity iff for extended rules
-- ===================================================================

-- retained: used by LCS.FirstOrder.Equality.Part2
/-- Lemma 5.4.2: For each one-premise rule of the §5.4.8 extended
G system, the conclusion sequent is falsifiable in M iff the premise
is. Parallel of Lemma 5.4.2 (`ruleFalsificationIff1`) under the §5.4.8
standing assumption. -/
theorem ruleFalsificationIff1Ext {L : Language} (M : Structure L)
    {prem conc : Sequent L} (rule : GentzenStep1Ext prem conc) :
    sequentFalsifiableIn M conc ↔ sequentFalsifiableIn M prem := by
-- BEGIN PROOF
  cases rule with
  | conjLeft Γ Δ Λ A B =>
    constructor
    · intro ⟨s, hant, hsucc⟩
      exact ⟨s, fun F hF => by
        rcases mem2_cases hF with h1 | h2 | h3 | h4
        · exact hant F (mem1_left h1)
        · rw [h2]; exact (hant _ mem1_center).1
        · rw [h3]; exact (hant _ mem1_center).2
        · exact hant F (mem1_right h4), hsucc⟩
    · intro ⟨s, hant, hsucc⟩
      exact ⟨s, fun F hF => by
        rcases mem1_cases hF with h1 | rfl | h3
        · exact hant F (mem2_left h1)
        · exact ⟨hant A mem2_first, hant B mem2_second⟩
        · exact hant F (mem2_right h3), hsucc⟩
  | disjRight Γ Δ Λ A B =>
    constructor
    · intro ⟨s, hant, hsucc⟩
      have hAB := hsucc _ mem1_center
      have hA : ¬ formulaEvalN M A s := fun h => hAB (Or.inl h)
      have hB : ¬ formulaEvalN M B s := fun h => hAB (Or.inr h)
      exact ⟨s, hant, fun F hF => by
        rcases mem2_cases hF with h1 | h2 | h3 | h4
        · exact hsucc F (mem1_left h1)
        · rw [h2]; exact hA
        · rw [h3]; exact hB
        · exact hsucc F (mem1_right h4)⟩
    · intro ⟨s, hant, hsucc⟩
      exact ⟨s, hant, fun F hF => by
        rcases mem1_cases hF with h1 | rfl | h3
        · exact hsucc F (mem2_left h1)
        · intro hAB; rcases hAB with hA | hB
          · exact hsucc A mem2_first hA
          · exact hsucc B mem2_second hB
        · exact hsucc F (mem2_right h3)⟩
  | implRight Γ Δ Λ A B =>
    constructor
    · intro ⟨s, hant, hsucc⟩
      have hAB := hsucc _ mem1_center
      have hA : formulaEvalN M A s :=
        Classical.byContradiction (fun hNA => hAB (fun h => absurd h hNA))
      have hB : ¬ formulaEvalN M B s := fun hB => hAB (fun _ => hB)
      exact ⟨s, fun F hF => by
        rcases memcons_cases hF with rfl | hF'
        · exact hA
        · exact hant F hF',
        fun F hF => by
        rcases memcons_cases hF with rfl | hCtx
        · exact hB
        · rcases memcat_cases hCtx with hΔ | hΛ
          · exact hsucc F (mem1_left hΔ)
          · exact hsucc F (mem1_right hΛ)⟩
    · intro ⟨s, hant, hsucc⟩
      exact ⟨s, fun F hF => hant F (memcons_tail hF), fun F hF => by
        rcases mem1_cases hF with h1 | rfl | h3
        · exact hsucc F (memcons_tail (memcat_left h1))
        · simp only [formulaEvalN]
          intro hAB
          exact absurd (hAB (hant A memcons_head)) (hsucc B memcons_head)
        · exact hsucc F (memcons_tail (memcat_right h3))⟩
  | negLeft Γ Δ Λ A =>
    constructor
    · intro ⟨s, hant, hsucc⟩
      have hNA := hant _ mem1_center
      exact ⟨s, fun F hF => by
        rcases memcat_cases hF with hΓ | hΔ
        · exact hant F (mem1_left hΓ)
        · exact hant F (mem1_right hΔ),
        fun F hF => by
        rcases memcons_cases hF with rfl | hΛ
        · exact hNA
        · exact hsucc F hΛ⟩
    · intro ⟨s, hant, hsucc⟩
      have hA := hsucc A memcons_head
      exact ⟨s, fun F hF => by
        rcases mem1_cases hF with h1 | rfl | h3
        · exact hant F (memcat_left h1)
        · exact hA
        · exact hant F (memcat_right h3), fun F hF => hsucc F (memcons_tail hF)⟩
  | negRight Γ Δ Λ A =>
    constructor
    · intro ⟨s, hant, hsucc⟩
      have hNA := hsucc _ mem1_center
      have hA : formulaEvalN M A s :=
        Classical.byContradiction (fun h => hNA h)
      exact ⟨s, fun F hF => by
        rcases memcons_cases hF with rfl | hF'
        · exact hA
        · exact hant F hF',
        fun F hF => by
        rcases memcat_cases hF with hΔ | hΛ
        · exact hsucc F (mem1_left hΔ)
        · exact hsucc F (mem1_right hΛ)⟩
    · intro ⟨s, hant, hsucc⟩
      have hA := hant A memcons_head
      exact ⟨s, fun F hF => hant F (memcons_tail hF),
        fun F hF => by
        rcases mem1_cases hF with h1 | rfl | h3
        · exact hsucc F (memcat_left h1)
        · intro hNA; exact absurd hA hNA
        · exact hsucc F (memcat_right h3)⟩
  | allLeft ts Γ Δ Λ x A hne hfree =>
    constructor
    · intro ⟨s, hant, hsucc⟩
      have hAll := hant _ mem1_center
      refine ⟨s, fun F hF => ?_, hsucc⟩
      rcases List.mem_append.mp hF with hFirst | hDelta
      · rcases List.mem_append.mp hFirst with hMid | hAllxA
        · rcases List.mem_append.mp hMid with hGamma | hMap
          · exact hant F (mem1_left hGamma)
          · obtain ⟨t_i, ht_i_mem, rfl⟩ := List.mem_map.mp hMap
            exact (formulaSubstEvalDirectN s A t_i x (hfree t_i ht_i_mem)).mpr
              (hAll (termEval M s t_i))
        · simp at hAllxA; rw [hAllxA]; exact hAll
      · exact hant F (mem1_right hDelta)
    · intro ⟨s, hant, hsucc⟩
      refine ⟨s, fun F hF => ?_, hsucc⟩
      rcases mem1_cases hF with h1 | rfl | h3
      · exact hant F
          (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h1)))
      · exact hant _
          (List.mem_append_left _ (List.mem_append_right _ (List.Mem.head _)))
      · exact hant F (List.mem_append_right _ h3)
  | allRight y Γ Δ Λ x A hfresh hfreeFor =>
    have hfreeY : isFreeForN (Term.var y) x A := hfreeFor
    have yA : ∀ z ∈ formulaFVN A, z ≠ x → z ≠ y := by
      intro z hz hzx hzy; subst hzy
      exact hfresh (FormulaN.all x A) (List.mem_append_right _ mem1_center) ⟨hz, hzx⟩
    constructor
    · intro ⟨s, hant, hsucc⟩
      have hAll := hsucc _ mem1_center
      have ⟨a, ha⟩ : ∃ a, ¬ formulaEvalN M A (assignUpdate s x a) :=
        Classical.byContradiction (fun h =>
          hAll (fun a => Classical.byContradiction (fun hna => h ⟨a, hna⟩)))
      let s' : Assignment M := assignUpdate s y a
      have coin_fresh : ∀ (F : FormulaN L), y ∉ formulaFVN F →
          ∀ z, z ∈ formulaFVN F → s z = (assignUpdate s y a) z := by
        intro F hyF z hz
        show s z = if z = y then a else s z
        split
        · rename_i hzy; exact absurd (hzy ▸ hz) hyF
        · rfl
      have coin_fresh_ant : ∀ F ∈ Γ, formulaEvalN M F s' := fun F hF =>
        (coincidenceLemmaN M F s s' (coin_fresh F
          (hfresh F (List.mem_append_left _ hF)))).mp (hant F hF)
      have coin_fresh_succ : ∀ F ∈ Δ ++ Λ, ¬ formulaEvalN M F s' := by
        intro F hF heval
        have hyF : y ∉ formulaFVN F := by
          rcases List.mem_append.mp hF with hD | hL
          · exact hfresh F (List.mem_append_right _ (mem1_left hD))
          · exact hfresh F (List.mem_append_right _ (mem1_right hL))
        have : formulaEvalN M F s := (coincidenceLemmaN M F s' s (fun z hz => by
          show assignUpdate s y a z = s z
          rw [coin_fresh F hyF z hz])).mp heval
        rcases List.mem_append.mp hF with hD | hL
        · exact hsucc F (mem1_left hD) this
        · exact hsucc F (mem1_right hL) this
      have coinA' : formulaEvalN M A (assignUpdate (assignUpdate s y a) x a) ↔
          formulaEvalN M A (assignUpdate s x a) :=
        coincidenceLemmaN M A _ _ (fun z hz => by
          simp only [assignUpdate]
          split
          · rfl
          · rename_i hzx; split
            · rename_i hzy; exact absurd hzy (yA z hz hzx)
            · rfl)
      have hAsub : ¬ formulaEvalN M (formulaSubstN A (Term.var y) x) s' := by
        intro heval
        rw [formulaSubstEvalDirectN s' A (Term.var y) x hfreeY] at heval
        have : termEval M s' (Term.var y) = a := by
          show assignUpdate s y a y = a
          simp only [assignUpdate, ite_true]
        rw [this] at heval
        exact ha (coinA'.mp heval)
      exact ⟨s', coin_fresh_ant, fun F hF => by
        rcases mem1_cases hF with h1 | rfl | h3
        · exact coin_fresh_succ F (List.mem_append_left _ h1)
        · exact hAsub
        · exact coin_fresh_succ F (List.mem_append_right _ h3)⟩
    · intro ⟨s, hant, hsucc⟩
      have hAsub := hsucc _ mem1_center
      have hNotA : ¬ formulaEvalN M A (assignUpdate s x (s y)) := by
        intro heval
        apply hAsub
        rw [formulaSubstEvalDirectN s A (Term.var y) x hfreeY]
        simp [termEval]; exact heval
      exact ⟨s, hant, fun F hF => by
        rcases mem1_cases hF with h1 | rfl | h3
        · exact hsucc F (mem1_left h1)
        · intro hall; exact hNotA (hall (s y))
        · exact hsucc F (mem1_right h3)⟩
  | exLeft y Γ Δ Λ x A hfresh hfreeFor =>
    have hfreeY : isFreeForN (Term.var y) x A := hfreeFor
    have yA : ∀ z ∈ formulaFVN A, z ≠ x → z ≠ y := by
      intro z hz hzx hzy; subst hzy
      exact hfresh (FormulaN.ex x A) (List.mem_append_left _ mem1_center) ⟨hz, hzx⟩
    constructor
    · intro ⟨s, hant, hsucc⟩
      have hExA := hant _ mem1_center
      obtain ⟨a, ha⟩ := hExA
      let s' : Assignment M := assignUpdate s y a
      have coin_fresh : ∀ (F : FormulaN L), y ∉ formulaFVN F →
          ∀ z, z ∈ formulaFVN F → s z = (assignUpdate s y a) z := by
        intro F hyF z hz
        show s z = if z = y then a else s z
        split
        · rename_i hzy; exact absurd (hzy ▸ hz) hyF
        · rfl
      have coin_fresh_ant : ∀ F ∈ Γ ++ Δ, formulaEvalN M F s' := by
        intro F hF
        have hyF : y ∉ formulaFVN F := by
          rcases List.mem_append.mp hF with hΓ | hΔ
          · exact hfresh F (List.mem_append_left _ (mem1_left hΓ))
          · exact hfresh F (List.mem_append_left _ (mem1_right hΔ))
        exact (coincidenceLemmaN M F s s' (coin_fresh F hyF)).mp (by
          rcases List.mem_append.mp hF with hΓ | hΔ
          · exact hant F (mem1_left hΓ)
          · exact hant F (mem1_right hΔ))
      have coin_fresh_succ : ∀ F ∈ Λ, ¬ formulaEvalN M F s' := by
        intro F hF heval
        have hyF : y ∉ formulaFVN F := hfresh F (List.mem_append_right _ hF)
        have : formulaEvalN M F s := (coincidenceLemmaN M F s' s (fun z hz => by
          rw [coin_fresh F hyF z hz])).mp heval
        exact hsucc F hF this
      have coinA : formulaEvalN M A (assignUpdate (assignUpdate s y a) x a) ↔
          formulaEvalN M A (assignUpdate s x a) :=
        coincidenceLemmaN M A _ _ (fun z hz => by
          simp only [assignUpdate]
          split
          · rfl
          · rename_i hzx; split
            · rename_i hzy; exact absurd hzy (yA z hz hzx)
            · rfl)
      have hAsub : formulaEvalN M (formulaSubstN A (Term.var y) x) s' := by
        rw [formulaSubstEvalDirectN s' A (Term.var y) x hfreeY]
        have : termEval M s' (Term.var y) = a := by
          show assignUpdate s y a y = a
          simp only [assignUpdate, ite_true]
        rw [this]
        exact coinA.mpr ha
      exact ⟨s', fun F hF => by
        rcases mem1_cases hF with h1 | rfl | h3
        · exact coin_fresh_ant F (List.mem_append_left _ h1)
        · exact hAsub
        · exact coin_fresh_ant F (List.mem_append_right _ h3), coin_fresh_succ⟩
    · intro ⟨s, hant, hsucc⟩
      have hAyx := hant _ mem1_center
      have hExA : formulaEvalN M (FormulaN.ex x A) s :=
        ⟨s y, (formulaSubstEvalDirectN s A (Term.var y) x hfreeY).mp hAyx⟩
      exact ⟨s, fun F hF => by
        rcases mem1_cases hF with h1 | rfl | h3
        · exact hant F (mem1_left h1)
        · exact hExA
        · exact hant F (mem1_right h3), hsucc⟩
  | exRight ts Γ Δ Λ x A hne hfree =>
    constructor
    · intro ⟨s, hant, hsucc⟩
      have hExA := hsucc _ mem1_center
      have hNotSub : ∀ t_i ∈ ts, ¬ formulaEvalN M (formulaSubstN A t_i x) s :=
        fun t_i ht_i h =>
          hExA ⟨termEval M s t_i,
            (formulaSubstEvalDirectN s A t_i x (hfree t_i ht_i)).mp h⟩
      refine ⟨s, hant, fun F hF => ?_⟩
      rcases List.mem_append.mp hF with hFirst | hLambda
      · rcases List.mem_append.mp hFirst with hMid | hExxA
        · rcases List.mem_append.mp hMid with hDelta | hMap
          · exact hsucc F (mem1_left hDelta)
          · obtain ⟨t_i, ht_i_mem, rfl⟩ := List.mem_map.mp hMap
            exact hNotSub t_i ht_i_mem
        · simp at hExxA; rw [hExxA]; exact hExA
      · exact hsucc F (mem1_right hLambda)
    · intro ⟨s, hant, hsucc⟩
      refine ⟨s, hant, fun F hF => ?_⟩
      rcases mem1_cases hF with h1 | rfl | h3
      · exact hsucc F
          (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h1)))
      · exact hsucc _
          (List.mem_append_left _ (List.mem_append_right _ (List.Mem.head _)))
      · exact hsucc F (List.mem_append_right _ h3)

-- retained: used by LCS.FirstOrder.Equality.Part2
/-- Lemma 5.4.2 (companion, two-premise): For each two-premise rule
of the §5.4.8 extended G system, the conclusion sequent is falsifiable
in M iff at least one premise is falsifiable. Parallel of Lemma 5.4.2
(`ruleFalsificationIff2`). -/
theorem ruleFalsificationIff2Ext {L : Language} (M : Structure L)
    {prem1 prem2 conc : Sequent L} (rule : GentzenStep2Ext prem1 prem2 conc) :
    sequentFalsifiableIn M conc ↔
    (sequentFalsifiableIn M prem1 ∨ sequentFalsifiableIn M prem2) := by
-- BEGIN PROOF
  cases rule with
  | conjRight Γ Δ Λ A B =>
    constructor
    · intro ⟨s, hant, hsucc⟩
      have hAB := hsucc _ mem1_center
      rcases Classical.em (formulaEvalN M A s) with hA | hA
      · right; exact ⟨s, hant, fun F hF => by
          rcases mem1_cases hF with h1 | rfl | h3
          · exact hsucc F (mem1_left h1)
          · exact fun hB => hAB ⟨hA, hB⟩
          · exact hsucc F (mem1_right h3)⟩
      · left; exact ⟨s, hant, fun F hF => by
          rcases mem1_cases hF with h1 | rfl | h3
          · exact hsucc F (mem1_left h1)
          · exact hA
          · exact hsucc F (mem1_right h3)⟩
    · intro h; rcases h with ⟨s, hant, hsucc⟩ | ⟨s, hant, hsucc⟩
      · have hA := hsucc _ mem1_center
        exact ⟨s, hant, fun F hF => by
          rcases mem1_cases hF with h1 | rfl | h3
          · exact hsucc F (mem1_left h1)
          · intro ⟨ha, _⟩; exact hA ha
          · exact hsucc F (mem1_right h3)⟩
      · have hB := hsucc _ mem1_center
        exact ⟨s, hant, fun F hF => by
          rcases mem1_cases hF with h1 | rfl | h3
          · exact hsucc F (mem1_left h1)
          · intro ⟨_, hb⟩; exact hB hb
          · exact hsucc F (mem1_right h3)⟩
  | disjLeft Γ Δ Λ A B =>
    constructor
    · intro ⟨s, hant, hsucc⟩
      have hAB := hant _ mem1_center
      rcases hAB with hA | hB
      · left; exact ⟨s, fun F hF => by
          rcases mem1_cases hF with h1 | rfl | h3
          · exact hant F (mem1_left h1)
          · exact hA
          · exact hant F (mem1_right h3), hsucc⟩
      · right; exact ⟨s, fun F hF => by
          rcases mem1_cases hF with h1 | rfl | h3
          · exact hant F (mem1_left h1)
          · exact hB
          · exact hant F (mem1_right h3), hsucc⟩
    · intro h; rcases h with ⟨s, hant, hsucc⟩ | ⟨s, hant, hsucc⟩
      · exact ⟨s, fun F hF => by
          rcases mem1_cases hF with h1 | rfl | h3
          · exact hant F (mem1_left h1)
          · exact Or.inl (hant A mem1_center)
          · exact hant F (mem1_right h3), hsucc⟩
      · exact ⟨s, fun F hF => by
          rcases mem1_cases hF with h1 | rfl | h3
          · exact hant F (mem1_left h1)
          · exact Or.inr (hant B mem1_center)
          · exact hant F (mem1_right h3), hsucc⟩
  | implLeft Γ Δ Λ A B =>
    constructor
    · intro ⟨s, hant, hsucc⟩
      have hAB := hant _ mem1_center
      rcases Classical.em (formulaEvalN M A s) with hA | hA
      · have hB := hAB hA
        right; exact ⟨s, fun F hF => by
          rcases memcons_cases hF with rfl | hF'
          · exact hB
          · rcases memcat_cases hF' with hΓ | hΔ
            · exact hant F (mem1_left hΓ)
            · exact hant F (mem1_right hΔ), hsucc⟩
      · left; exact ⟨s, fun F hF => by
          rcases memcat_cases hF with hΓ | hΔ
          · exact hant F (mem1_left hΓ)
          · exact hant F (mem1_right hΔ),
          fun F hF => by
          rcases memcons_cases hF with rfl | hΛ
          · exact hA
          · exact hsucc F hΛ⟩
    · intro h; rcases h with ⟨s, hant, hsucc⟩ | ⟨s, hant, hsucc⟩
      · have hA := hsucc A memcons_head
        exact ⟨s, fun F hF => by
          rcases mem1_cases hF with h1 | rfl | h3
          · exact hant F (memcat_left h1)
          · intro hA'; exact absurd hA' hA
          · exact hant F (memcat_right h3),
          fun F hF => hsucc F (memcons_tail hF)⟩
      · have hB := hant B memcons_head
        exact ⟨s, fun F hF => by
          rcases mem1_cases hF with h1 | rfl | h3
          · exact hant F (memcons_tail (memcat_left h1))
          · intro _; exact hB
          · exact hant F (memcons_tail (memcat_right h3)), hsucc⟩

-- retained: used by LCS.FirstOrder.Equality.Part2
/-- Lemma 5.4.2 (companion): For each one-premise rule of the §5.4.8
extended G system, the conclusion sequent is valid iff the premise is
valid. Parallel of Lemma 5.4.2 (`ruleValidityIff1`). -/
theorem ruleValidityIff1Ext {L : Language}
    {prem conc : Sequent L} (rule : GentzenStep1Ext prem conc) :
    sequentValid conc ↔ sequentValid prem := by
-- BEGIN PROOF
  rw [sequentValid_iff_not_falsifiable, sequentValid_iff_not_falsifiable]
  exact forall_congr' (fun M => not_congr (ruleFalsificationIff1Ext M rule))

-- retained: used by LCS.FirstOrder.Equality.Part2
/-- Lemma 5.4.2 (companion): For each two-premise rule of the §5.4.8
extended G system, the conclusion sequent is valid iff both premises
are valid. Parallel of Lemma 5.4.2 (`ruleValidityIff2`). -/
theorem ruleValidityIff2Ext {L : Language}
    {prem1 prem2 conc : Sequent L} (rule : GentzenStep2Ext prem1 prem2 conc) :
    sequentValid conc ↔ (sequentValid prem1 ∧ sequentValid prem2) := by
-- BEGIN PROOF
  rw [sequentValid_iff_not_falsifiable, sequentValid_iff_not_falsifiable,
      sequentValid_iff_not_falsifiable]
  constructor
  · intro h
    constructor
    · intro M hp1
      exact h M ((ruleFalsificationIff2Ext M rule).mpr (Or.inl hp1))
    · intro M hp2
      exact h M ((ruleFalsificationIff2Ext M rule).mpr (Or.inr hp2))
  · rintro ⟨h1, h2⟩ M hconc
    rcases (ruleFalsificationIff2Ext M rule).mp hconc with hp1 | hp2
    · exact h1 M hp1
    · exact h2 M hp2

-- ===================================================================
-- Lemma 5.4.3: Soundness of G under the §5.4.8 standing assumption
-- ===================================================================

-- retained: used by LCS.CutElim.Robinson, LCS.FirstOrder.Completeness, LCS.FirstOrder.Completeness.MetaTheorems, LCS.FirstOrder.Equality.Part2, LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- Lemma 5.4.3 (companion): Every `GProofTreeExt` has a valid
conclusion sequent. Proved by induction on the tree, using
`ruleValidityIff1Ext`/`ruleValidityIff2Ext` (Lemma 5.4.2) for the
inductive steps. Parallel of `proofTreeValid` (Lem 5.4.3) on the
§5.4.8 extended proof-tree type. -/
theorem proofTreeValid_Ext {L : Language} {s : Sequent L}
    (t : GProofTreeExt s) : sequentValid s := by
-- BEGIN PROOF
  induction t with
  | axiom_ s hax =>
    intro M as hant
    obtain ⟨A, hA_ant, hA_suc⟩ := hax
    exact ⟨A, hA_suc, hant A hA_ant⟩
  | onePremise rule _ ih =>
    exact (ruleValidityIff1Ext rule).mpr ih
  | twoPremise rule _ _ ih1 ih2 =>
    exact (ruleValidityIff2Ext rule).mpr ⟨ih1, ih2⟩

-- retained: used by LCS.CutElim.Robinson, LCS.FirstOrder.Completeness, LCS.FirstOrder.Completeness.MetaTheorems, LCS.FirstOrder.Equality.Part2, LCS.FirstOrder.Gentzen.Search.NoFunction.Search
/-- Lemma 5.4.3: Soundness of G under the §5.4.8 standing assumption.
If a sequent is G-provable in the sense of `sequentProvableExt` (there
exists a `GProofTreeExt` with that conclusion), then the sequent is
valid. Parallel of `soundnessG` (Lem 5.4.3) on the §5.4.8 extended
rule system. -/
theorem soundnessG_Ext {L : Language} (seq : Sequent L)
    (h : sequentProvableExt seq) : sequentValid seq := by
-- BEGIN PROOF
  obtain ⟨t⟩ := h
  exact proofTreeValid_Ext t













/-- Theorem 5.5.1 (input convention): An empty marker terminates a finite
formula sequence; a sequence with no empty marker is countably infinite. -/
@[blueprint "chap5__definition_5_5_1"]
def NoHolesN {L : Language} (a : Nat → Option (FormulaN L)) : Prop :=
  ∀ n, a n = none → a (n + 1) = none

/-- Theorem 5.5.1 (input): A possibly infinite sequent has two ordered
formula sequences, each finite or countably infinite, with no holes. -/
@[blueprint "chap5__definition_5_5_1"]
structure InfSequentN (L : Language) where
  antecedent : Nat → Option (FormulaN L)
  succedent : Nat → Option (FormulaN L)
  antecedent_noHoles : NoHolesN antecedent
  succedent_noHoles : NoHolesN succedent

/-- Theorem 5.5.1 (input): Embed a finite sequent by terminating each list
with empty markers. -/
@[blueprint "chap5__definition_5_5_1"]
def InfSequentN.ofSequent {L : Language} (s : Sequent L) : InfSequentN L where
  antecedent := fun n => s.antecedent[n]?
  succedent := fun n => s.succedent[n]?
  antecedent_noHoles := by
    intro n hn
    have h := List.getElem?_eq_none_iff.mp hn
    exact List.getElem?_eq_none (by omega)
  succedent_noHoles := by
    intro n hn
    have h := List.getElem?_eq_none_iff.mp hn
    exact List.getElem?_eq_none (by omega)

/-- Theorem 5.5.1 (input): Membership in the antecedent means occurrence
at some finite position. -/
@[blueprint "chap5__definition_5_5_1"]
def InfSequentN.memAntecedent {L : Language} (q : InfSequentN L) (A : FormulaN L) : Prop :=
  ∃ n, q.antecedent n = some A

/-- Theorem 5.5.1 (input): Membership in the succedent means occurrence
at some finite position. -/
@[blueprint "chap5__definition_5_5_1"]
def InfSequentN.memSuccedent {L : Language} (q : InfSequentN L) (A : FormulaN L) : Prop :=
  ∃ n, q.succedent n = some A

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Finite embedding preserves antecedent membership. -/
theorem InfSequentN.memAntecedent_ofSequent {L : Language} (s : Sequent L) (A : FormulaN L) :
    (ofSequent s).memAntecedent A ↔ A ∈ s.antecedent := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hn
    exact List.mem_iff_getElem.mpr ⟨n, hlt, heq⟩
  · intro hA
    obtain ⟨n, hlt, heq⟩ := List.mem_iff_getElem.mp hA
    exact ⟨n, List.getElem?_eq_some_iff.mpr ⟨hlt, heq⟩⟩

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Finite embedding preserves succedent membership. -/
theorem InfSequentN.memSuccedent_ofSequent {L : Language} (s : Sequent L) (A : FormulaN L) :
    (ofSequent s).memSuccedent A ↔ A ∈ s.succedent := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hn
    exact List.mem_iff_getElem.mpr ⟨n, hlt, heq⟩
  · intro hA
    obtain ⟨n, hlt, heq⟩ := List.mem_iff_getElem.mp hA
    exact ⟨n, List.getElem?_eq_some_iff.mpr ⟨hlt, heq⟩⟩

/-- Theorem 5.5.1, using Definition 3.5.2: Validity means that in every
structure and assignment, truth of every antecedent member implies truth
of some succedent member. -/
@[blueprint "chap5__theorem_5_5_1"]
def infSequentValid {L : Language} (q : InfSequentN L) : Prop :=
  ∀ (M : Structure L) (s : Assignment M),
    (∀ A, q.memAntecedent A → formulaEvalN M A s) →
    ∃ B, q.memSuccedent B ∧ formulaEvalN M B s

/-- Theorem 5.5.1, using Definition 3.5.2: Falsifiability means that some
structure and assignment satisfy every antecedent member and falsify every
succedent member. -/
@[blueprint "chap5__theorem_5_5_1"]
def infSequentFalsifiable {L : Language} (q : InfSequentN L) : Prop :=
  ∃ (M : Structure L) (s : Assignment M),
    (∀ A, q.memAntecedent A → formulaEvalN M A s) ∧
    (∀ B, q.memSuccedent B → ¬ formulaEvalN M B s)

-- retained: used by LCS.FirstOrder.Completeness
/-- Finite embedding preserves validity. -/
theorem infSequentValid_ofSequent_iff {L : Language} (s : Sequent L) :
    infSequentValid (InfSequentN.ofSequent s) ↔ sequentValid s := by
  simp only [infSequentValid, sequentValid, InfSequentN.memAntecedent_ofSequent,
    InfSequentN.memSuccedent_ofSequent]

/-- Theorem 5.5.1 (standing assumption): No variable free in any formula
on either side occurs bound in any formula on either side. -/
@[blueprint "chap5__definition_5_5_1"]
def crossNoFreeBoundInf {L : Language} (q : InfSequentN L) : Prop :=
  ∀ x : Nat,
    (∃ A, (q.memAntecedent A ∨ q.memSuccedent A) ∧ x ∈ formulaFVN A) →
    ∀ B, (q.memAntecedent B ∨ q.memSuccedent B) → x ∉ formulaBVN B

end LCS.FirstOrder.Gentzen
end

section
namespace LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Substitution

/-- Definition 5.4.8 (companion): A deduction with the indicated sole
    premise leaf and exactly `k` single-term quantifier steps. `false`
    selects only ∀:left steps; `true` selects only ∃:right steps. -/
@[blueprint "chap5__definition_5_4_8"]
inductive GDeductionTree.QuantifierChain {L : Language} (hL : L.withoutEquality)
    (prem : Sequent L) : Bool → Nat → {conc : Sequent L} → GDeductionTree hL conc → Prop where
  | leaf (right : Bool) : QuantifierChain hL prem right 0 (.leaf prem)
  | allLeft (t : Term L) (Γ Δ Λ : List (FormulaN L)) (x : Nat) (A : FormulaN L)
      (hfree : isFreeForN t x A) {k : Nat}
      {tree : GDeductionTree hL (.mk (Γ ++ [formulaSubstN A t x, .all x A] ++ Δ) Λ)}
      (h : QuantifierChain hL prem false k tree) :
      QuantifierChain hL prem false (k + 1)
        (.onePremise (.allLeft t Γ Δ Λ x A hfree) tree)
  | exRight (t : Term L) (Γ Δ Λ : List (FormulaN L)) (x : Nat) (A : FormulaN L)
      (hfree : isFreeForN t x A) {k : Nat}
      {tree : GDeductionTree hL (.mk Γ (Δ ++ [formulaSubstN A t x, .ex x A] ++ Λ))}
      (h : QuantifierChain hL prem true k tree) :
      QuantifierChain hL prem true (k + 1)
        (.onePremise (.exRight t Γ Δ Λ x A hfree) tree)

/-- Definition 5.4.8 (companion): Number of terms in an extended ∀:left instance. -/
@[blueprint "chap5__definition_5_4_8"]
def ExtendedAllLeft.termCount {L : Language} {prem conc : Sequent L}
    (rule : ExtendedAllLeft prem conc) : Nat :=
  match rule with | .mk ts _ _ _ _ _ _ _ => ts.length

/-- Definition 5.4.8 (companion): Number of terms in an extended ∃:right instance. -/
@[blueprint "chap5__definition_5_4_8"]
def ExtendedExRight.termCount {L : Language} {prem conc : Sequent L}
    (rule : ExtendedExRight prem conc) : Nat :=
  match rule with | .mk ts _ _ _ _ _ _ _ => ts.length





/-- Definition 5.4.8 (companion): Each extended ∀:left instance is simulated
    from its premise by a one-leaf deduction of exactly k ordinary ∀:left steps. -/
@[blueprint "chap5__definition_5_4_8"]
theorem ExtendedAllLeft.simulateInference {L : Language} (hL : L.withoutEquality)
    {prem conc : Sequent L} (rule : ExtendedAllLeftNoEq hL prem conc) :
    ∃ tree : GDeductionTree hL conc,
      tree.QuantifierChain hL prem false rule.termCount 

/-- Definition 5.4.8 (companion): Each extended ∃:right instance is simulated
    from its premise by a one-leaf deduction of exactly k ordinary ∃:right steps. -/
@[blueprint "chap5__definition_5_4_8"]
theorem ExtendedExRight.simulateInference {L : Language} (hL : L.withoutEquality)
    {prem conc : Sequent L} (rule : ExtendedExRightNoEq hL prem conc) :
    ∃ tree : GDeductionTree hL conc,
      tree.QuantifierChain hL prem true rule.termCount 

end LCS.FirstOrder.Gentzen
end

