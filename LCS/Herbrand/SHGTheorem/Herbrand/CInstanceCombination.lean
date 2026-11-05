import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.Herbrand.NNFHauptsatz.Equality
import LCS.Herbrand.SHGTheorem.Herbrand.SyntaxAllocation
import LCS.Herbrand.SHGTheorem.Herbrand.OccurrenceLineage
import LCS.Herbrand.SHGTheorem.Herbrand.CanonicalMapRegression
import LCS.Herbrand.SHGTheorem.Herbrand.NestedMapRegression
import LCS.Herbrand.SHGTheorem.Herbrand.Alteration
import Attach
import LCS.Herbrand.SHGTheorem.Herbrand.CInstanceCombination.ProofsStamp

section
namespace LCS.Herbrand.SHGTheorem.Herbrand
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.SHGTheorem
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.Equality
open LCS.Herbrand.SharpenedHauptsatz
open LCS.CutElim.Hauptsatz
open LCS.Herbrand.PrenexForm
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae

-- ATTACH-BLOCKER: private declaration
private def g2nnfCombineDisj {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (X Y A B C D : FormulaN L)
    (hXQF : isQuantifierFree X) (hYQF : isQuantifierFree Y)
    (hAQF : isQuantifierFree A) (hBQF : isQuantifierFree B)
    (hCQF : isQuantifierFree C) (hDQF : isQuantifierFree D)
    (p : G2nnfProofTree hNoEq
      ({X} : G2FormulaFinset)
      ({FormulaN.conj A B} : G2FormulaFinset))
    (q : G2nnfProofTree hNoEq
      ({Y} : G2FormulaFinset)
      ({FormulaN.conj C D} : G2FormulaFinset))
    (idA : G2nnfProofTree hNoEq
      ({A} : G2FormulaFinset) ({A} : G2FormulaFinset))
    (idB : G2nnfProofTree hNoEq
      ({B} : G2FormulaFinset) ({B} : G2FormulaFinset))
    (idC : G2nnfProofTree hNoEq
      ({C} : G2FormulaFinset) ({C} : G2FormulaFinset))
    (idD : G2nnfProofTree hNoEq
      ({D} : G2FormulaFinset) ({D} : G2FormulaFinset)) :
    G2nnfProofTree hNoEq
      ({FormulaN.disj X Y} : G2FormulaFinset)
      ({FormulaN.conj (FormulaN.disj A C) (FormulaN.disj B D)} :
        G2FormulaFinset) := by
  have hXNNF : FormulaN.isNNF X :=
    (G2nnfDeductionTreeCore.allNNF p).1 X
      ((LCS.Finset.mem_singleton X X).mpr rfl)
  have hYNNF : FormulaN.isNNF Y :=
    (G2nnfDeductionTreeCore.allNNF q).1 Y
      ((LCS.Finset.mem_singleton Y Y).mpr rfl)
  have hANNF : FormulaN.isNNF A :=
    (G2nnfDeductionTreeCore.allNNF idA).1 A
      ((LCS.Finset.mem_singleton A A).mpr rfl)
  have hBNNF : FormulaN.isNNF B :=
    (G2nnfDeductionTreeCore.allNNF idB).1 B
      ((LCS.Finset.mem_singleton B B).mpr rfl)
  have hCNNF : FormulaN.isNNF C :=
    (G2nnfDeductionTreeCore.allNNF idC).1 C
      ((LCS.Finset.mem_singleton C C).mpr rfl)
  have hDNNF : FormulaN.isNNF D :=
    (G2nnfDeductionTreeCore.allNNF idD).1 D
      ((LCS.Finset.mem_singleton D D).mpr rfl)
  have hXRect : isRectified X :=
    AllRectified.isRectified_of_isQuantifierFree X hXQF
  have hYRect : isRectified Y :=
    AllRectified.isRectified_of_isQuantifierFree Y hYQF
  have hABRect : isRectified (.conj A B) :=
    AllRectified.isRectified_of_isQuantifierFree (.conj A B)
      ⟨hAQF, hBQF⟩
  have hCDRect : isRectified (.conj C D) :=
    AllRectified.isRectified_of_isQuantifierFree (.conj C D)
      ⟨hCQF, hDQF⟩
  have hXYRect : isRectified (.disj X Y) :=
    AllRectified.isRectified_of_isQuantifierFree (.disj X Y)
      ⟨hXQF, hYQF⟩
  have hACRect : isRectified (.disj A C) :=
    AllRectified.isRectified_of_isQuantifierFree (.disj A C)
      ⟨hAQF, hCQF⟩
  have hBDRect : isRectified (.disj B D) :=
    AllRectified.isRectified_of_isQuantifierFree (.disj B D)
      ⟨hBQF, hDQF⟩
  have hTargetRect :
      isRectified (.conj (.disj A C) (.disj B D)) :=
    AllRectified.isRectified_of_isQuantifierFree
      (.conj (.disj A C) (.disj B D))
      ⟨⟨hAQF, hCQF⟩, ⟨hBQF, hDQF⟩⟩
  have pA :
      G2nnfProofTree hNoEq
        ({X} : G2FormulaFinset) ({A} : G2FormulaFinset) :=
    g2nnfCompose (hL := hNoEq) X (.conj A B) A p
      (g2nnfConjProjLeft (hNoEq := hNoEq) A B ⟨hANNF, hBNNF⟩ hABRect idA)
  have pB :
      G2nnfProofTree hNoEq
        ({X} : G2FormulaFinset) ({B} : G2FormulaFinset) :=
    g2nnfCompose (hL := hNoEq) X (.conj A B) B p
      (g2nnfConjProjRight (hNoEq := hNoEq) A B ⟨hANNF, hBNNF⟩ hABRect idB)
  have qC :
      G2nnfProofTree hNoEq
        ({Y} : G2FormulaFinset) ({C} : G2FormulaFinset) :=
    g2nnfCompose (hL := hNoEq) Y (.conj C D) C q
      (g2nnfConjProjLeft (hNoEq := hNoEq) C D ⟨hCNNF, hDNNF⟩ hCDRect idC)
  have qD :
      G2nnfProofTree hNoEq
        ({Y} : G2FormulaFinset) ({D} : G2FormulaFinset) :=
    g2nnfCompose (hL := hNoEq) Y (.conj C D) D q
      (g2nnfConjProjRight (hNoEq := hNoEq) C D ⟨hCNNF, hDNNF⟩ hCDRect idD)
  have leftA :
      G2nnfProofTree hNoEq
        ({X} : G2FormulaFinset)
        ({FormulaN.disj A C} : G2FormulaFinset) :=
    .onePremise (.disjRight1 A C ({X} : G2FormulaFinset) ∅) trivial rfl
      ⟨trivial, allNNF_singletons hXNNF ⟨hANNF, hCNNF⟩,
      (by intro seq h
          simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h
          subst seq; exact G2nnfDeductionTreeCore.allNNF pA),
      allRectified_singletons hXRect hACRect⟩
    pA
  have leftC :
      G2nnfProofTree hNoEq
        ({Y} : G2FormulaFinset)
        ({FormulaN.disj A C} : G2FormulaFinset) :=
    .onePremise (.disjRight2 A C ({Y} : G2FormulaFinset) ∅) trivial rfl
      ⟨trivial, allNNF_singletons hYNNF ⟨hANNF, hCNNF⟩,
      (by intro seq h
          simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h
          subst seq; exact G2nnfDeductionTreeCore.allNNF qC),
      allRectified_singletons hYRect hACRect⟩
    qC
  have left :
      G2nnfProofTree hNoEq
        ({FormulaN.disj X Y} : G2FormulaFinset)
        ({FormulaN.disj A C} : G2FormulaFinset) :=
    .twoPremise (.disjLeft X Y ∅ ({FormulaN.disj A C} : G2FormulaFinset)) trivial
      rfl
      ⟨trivial, allNNF_singletons ⟨hXNNF, hYNNF⟩ ⟨hANNF, hCNNF⟩,
      (by intro seq h
          simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl
          exact G2nnfDeductionTreeCore.allNNF leftA
          exact G2nnfDeductionTreeCore.allNNF leftC),
      allRectified_singletons hXYRect hACRect⟩
    leftA leftC
  have rightB :
      G2nnfProofTree hNoEq
        ({X} : G2FormulaFinset)
        ({FormulaN.disj B D} : G2FormulaFinset) :=
    .onePremise (.disjRight1 B D ({X} : G2FormulaFinset) ∅) trivial rfl
      ⟨trivial, allNNF_singletons hXNNF ⟨hBNNF, hDNNF⟩,
      (by intro seq h
          simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h
          subst seq; exact G2nnfDeductionTreeCore.allNNF pB),
      allRectified_singletons hXRect hBDRect⟩
    pB
  have rightD :
      G2nnfProofTree hNoEq
        ({Y} : G2FormulaFinset)
        ({FormulaN.disj B D} : G2FormulaFinset) :=
    .onePremise (.disjRight2 B D ({Y} : G2FormulaFinset) ∅) trivial rfl
      ⟨trivial, allNNF_singletons hYNNF ⟨hBNNF, hDNNF⟩,
      (by intro seq h
          simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h
          subst seq; exact G2nnfDeductionTreeCore.allNNF qD),
      allRectified_singletons hYRect hBDRect⟩
    qD
  have right :
      G2nnfProofTree hNoEq
        ({FormulaN.disj X Y} : G2FormulaFinset)
        ({FormulaN.disj B D} : G2FormulaFinset) :=
    .twoPremise (.disjLeft X Y ∅ ({FormulaN.disj B D} : G2FormulaFinset)) trivial
      rfl
      ⟨trivial, allNNF_singletons ⟨hXNNF, hYNNF⟩ ⟨hBNNF, hDNNF⟩,
      (by intro seq h
          simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl
          exact G2nnfDeductionTreeCore.allNNF rightB
          exact G2nnfDeductionTreeCore.allNNF rightD),
      allRectified_singletons hXYRect hBDRect⟩
    rightB rightD
  exact .twoPremise (.conjRight (.disj A C) (.disj B D) ({FormulaN.disj X Y} : G2FormulaFinset) ∅) trivial
    rfl
    ⟨trivial, allNNF_singletons ⟨hXNNF, hYNNF⟩ ⟨⟨hANNF, hCNNF⟩, ⟨hBNNF, hDNNF⟩⟩,
      (by intro seq h
          simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl
          exact G2nnfDeductionTreeCore.allNNF left
          exact G2nnfDeductionTreeCore.allNNF right),
      allRectified_singletons hXYRect hTargetRect⟩
    left right

-- ===================================================================
-- Lemma 7.6.1 (companion theorem): g2nnfCInstanceCombinationConnective
-- ===================================================================

-- ATTACH-BLOCKER: private name in relocated declaration
/-- Lemma 7.6.1 (companion theorem): Case (ii): if A = (B * C) where * is conjunction or disjunction, then K = (B_1 * C_1) and L = (B_2 * C_2). By the induction hypothesis, there exist c-instances D_1 of B and D_2 of C with D_1 implies (B_1 and B_2) and D_2 implies (C_1 and C_2) provable. Then D = (D_1 * D_2) is a c-instance of A and D implies (K and L) is provable. -/
theorem g2nnfCInstanceCombinationConnective {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (B C : FormulaN L)
    (isConj : Bool)
    (ihB : ∀ K' Ls', isCInstanceOf K' B → isCInstanceOf Ls' B →
      ∃ D', isCInstanceOf D' B ∧
        Nonempty (G2nnfProofTree hNoEq
          ({D'} : LCS.Finset (FormulaN L))
          ({FormulaN.conj K' Ls'} : LCS.Finset (FormulaN L))))
    (ihC : ∀ K' Ls', isCInstanceOf K' C → isCInstanceOf Ls' C →
      ∃ D', isCInstanceOf D' C ∧
        Nonempty (G2nnfProofTree hNoEq
          ({D'} : LCS.Finset (FormulaN L))
          ({FormulaN.conj K' Ls'} : LCS.Finset (FormulaN L))))
    (A : FormulaN L)
    (hA : A = if isConj then FormulaN.conj B C
              else FormulaN.disj B C)
    (K Ls : FormulaN L)
    (hK : isCInstanceOf K A)
    (hL : isCInstanceOf Ls A) :
    ∃ D, isCInstanceOf D A ∧
      Nonempty (G2nnfProofTree hNoEq
        ({D} : LCS.Finset (FormulaN L))
        ({FormulaN.conj K Ls} : LCS.Finset (FormulaN L))) := by
-- BEGIN PROOF
  subst A
  obtain ⟨kB, kC, hkBsrc, hkCsrc, hkBwf, hkCwf, hKform⟩ :=
    cinstance_connective_decompose isConj B C K hK
  obtain ⟨lB, lC, hlBsrc, hlCsrc, hlBwf, hlCwf, hLform⟩ :=
    cinstance_connective_decompose isConj B C Ls hL
  have hkB : isCInstanceOf kB.toFormula B :=
    ⟨kB, hkBsrc, rfl, hkBwf⟩
  have hlB : isCInstanceOf lB.toFormula B :=
    ⟨lB, hlBsrc, rfl, hlBwf⟩
  have hkC : isCInstanceOf kC.toFormula C :=
    ⟨kC, hkCsrc, rfl, hkCwf⟩
  have hlC : isCInstanceOf lC.toFormula C :=
    ⟨lC, hlCsrc, rfl, hlCwf⟩
  obtain ⟨D1, hD1, ⟨tB⟩⟩ :=
    ihB kB.toFormula lB.toFormula hkB hlB
  obtain ⟨D2, hD2, ⟨tC⟩⟩ :=
    ihC kC.toFormula lC.toFormula hkC hlC
  obtain ⟨dB, hdBsrc, hdBform, hdBwf⟩ := hD1
  obtain ⟨dC, hdCsrc, hdCform, hdCwf⟩ := hD2
  obtain ⟨idkB⟩ := g2nnf_identity_qf (hL := hNoEq) kB.toFormula
    (cInstance_toFormula_isNNF kB) (CInstance.isQuantifierFree kB)
  obtain ⟨idlB⟩ := g2nnf_identity_qf (hL := hNoEq) lB.toFormula
    (cInstance_toFormula_isNNF lB) (CInstance.isQuantifierFree lB)
  obtain ⟨idkC⟩ := g2nnf_identity_qf (hL := hNoEq) kC.toFormula
    (cInstance_toFormula_isNNF kC) (CInstance.isQuantifierFree kC)
  obtain ⟨idlC⟩ := g2nnf_identity_qf (hL := hNoEq) lC.toFormula
    (cInstance_toFormula_isNNF lC) (CInstance.isQuantifierFree lC)
  have hD1QF : isQuantifierFree D1 := by
    rw [← hdBform]
    exact CInstance.isQuantifierFree dB
  have hD2QF : isQuantifierFree D2 := by
    rw [← hdCform]
    exact CInstance.isQuantifierFree dC
  cases isConj with
  | false =>
      subst K
      subst Ls
      refine ⟨.disj D1 D2, ?_, ?_⟩
      · refine ⟨CInstance.connective false B C dB dC, rfl, ?_, ?_⟩
        · simp only [CInstance.toFormula, hdBform, hdCform]
        · exact ⟨hdBsrc, hdCsrc, hdBwf, hdCwf⟩
      · exact ⟨g2nnfCombineDisj (hNoEq := hNoEq) D1 D2
          kB.toFormula lB.toFormula kC.toFormula lC.toFormula
          hD1QF hD2QF
          (CInstance.isQuantifierFree kB)
          (CInstance.isQuantifierFree lB)
          (CInstance.isQuantifierFree kC)
          (CInstance.isQuantifierFree lC)
          tB tC idkB idlB idkC idlC⟩
  | true =>
      subst K
      subst Ls
      refine ⟨.conj D1 D2, ?_, ?_⟩
      · refine ⟨CInstance.connective true B C dB dC, rfl, ?_, ?_⟩
        · simp only [CInstance.toFormula, hdBform, hdCform]
        · exact ⟨hdBsrc, hdCsrc, hdBwf, hdCwf⟩
      · exact ⟨g2nnfCombineConj (hNoEq := hNoEq) D1 D2
          kB.toFormula lB.toFormula kC.toFormula lC.toFormula
          hD1QF hD2QF
          (CInstance.isQuantifierFree kB)
          (CInstance.isQuantifierFree lB)
          (CInstance.isQuantifierFree kC)
          (CInstance.isQuantifierFree lC)
          tB tC idkB idlB idkC idlC⟩

-- ATTACH-BLOCKER: private declaration
private theorem cinstance_all_decompose {L : Language}
    (x : Nat) (C K : FormulaN L)
    (hK : isCInstanceOf K (FormulaN.all x C)) :
    ∃ (t₀ : Term L) (h₀ : CInstance L)
      (tsRest : List (Term L)) (hsRest : List (CInstance L))
      (_hGround₀ : Term.isClosed t₀)
      (_hGroundRest : ∀ t ∈ tsRest, Term.isClosed t),
      h₀.source = formulaSubstN C t₀ x ∧
      CInstance.WellFormed h₀ ∧
      CInstance.WellFormedList x C tsRest hsRest ∧
      (hsRest.map CInstance.toFormula).foldr
        (fun f rest first => FormulaN.conj first (rest f)) id h₀.toFormula = K := by
  obtain ⟨ci, hSrc, hForm, hWF⟩ := hK
  cases ci with
  | atom A hAtom =>
      simp only [CInstance.source] at hSrc
      rw [hSrc] at hAtom
      cases hAtom
  | negAtom A hAtom =>
      simp only [CInstance.source] at hSrc
      cases hSrc
  | connective star B D H J =>
      cases star <;>
        simp only [CInstance.source] at hSrc <;>
        cases hSrc
  | forallInst y D t₀ h₀ tsRest hsRest hGround₀ hGroundRest =>
      simp only [CInstance.source] at hSrc
      cases hSrc
      simp only [CInstance.toFormula] at hForm
      exact ⟨t₀, h₀, tsRest, hsRest, hGround₀, hGroundRest,
        hWF.1, hWF.2.1, hWF.2.2, hForm⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem isCInstanceOf_isNNF {L : Language}
    (H B : FormulaN L) (h : isCInstanceOf H B) :
    FormulaN.isNNF H := by
  obtain ⟨ci, _hSrc, hForm, _hWF⟩ := h
  rw [← hForm]
  exact cInstance_toFormula_isNNF ci

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem isCInstanceOf_isQuantifierFree {L : Language}
    (H B : FormulaN L) (h : isCInstanceOf H B) :
    LCS.FirstOrder.SemanticsN.isQuantifierFree H := by
  obtain ⟨ci, _hSrc, hForm, _hWF⟩ := h
  rw [← hForm]
  exact CInstance.isQuantifierFree ci

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- A right-associated conjunction of quantifier-free formulae is
quantifier-free. -/
theorem listConj_isQuantifierFree {L : Language}
    (head : FormulaN L) (tail : List (FormulaN L))
    (hHead : isQuantifierFree head)
    (hTail : ∀ f, f ∈ tail → isQuantifierFree f) :
    isQuantifierFree (listConj head tail) := by
  induction tail generalizing head with
  | nil =>
      exact hHead
  | cons next rest ih =>
      exact ⟨hHead,
        ih next
          (hTail next List.mem_cons_self)
          (fun f hf => hTail f
            (List.mem_cons.mpr (Or.inr hf)))⟩

-- ATTACH-BLOCKER: private declaration
/-- The universal-instance fold agrees with the nonempty right-associated list. -/
private theorem rightConj_eq_listConj {L : Language}
    (fs : List (FormulaN L)) (head : FormulaN L) :
    fs.foldr (fun f rest first => FormulaN.conj first (rest f)) id head =
      listConj head fs := by
  induction fs generalizing head with
  | nil => rfl
  | cons f rest ih => simp only [List.foldr_cons, listConj, ih]

-- ATTACH-BLOCKER: private declaration
/-- Grouping a nonempty final suffix preserves the ordered conjunction. -/
private theorem listConj_suffix {L : Language}
    (fs : List (FormulaN L)) (head next : FormulaN L) (rest : List (FormulaN L)) :
    listConj head (fs ++ next :: rest) =
      listConj head (fs ++ [listConj next rest]) := by
  induction fs generalizing head with
  | nil => rfl
  | cons f tail ih => simp only [List.cons_append, listConj, ih]

-- ATTACH-BLOCKER: private declaration
/-- The ordered concatenation entails each of its two nonempty groups. -/
private theorem g2nnf_right_conj_split {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)] (fs : List (FormulaN L)) (head suffix : FormulaN L)
    (hHeadNNF : head.isNNF) (hSuffixNNF : suffix.isNNF)
    (hFsNNF : ∀ f ∈ fs, FormulaN.isNNF f)
    (hHeadQF : isQuantifierFree head) (hSuffixQF : isQuantifierFree suffix)
    (hFsQF : ∀ f ∈ fs, isQuantifierFree f) :
    Nonempty (G2nnfProofTree hNoEq {listConj head (fs ++ [suffix])} {listConj head fs}) ∧
    Nonempty (G2nnfProofTree hNoEq {listConj head (fs ++ [suffix])} {suffix}) := by
  induction fs generalizing head with
  | nil =>
    obtain ⟨ih⟩ := g2nnf_identity_qf (hL := hNoEq) head hHeadNNF hHeadQF
    obtain ⟨is⟩ := g2nnf_identity_qf (hL := hNoEq) suffix hSuffixNNF hSuffixQF
    have hr := AllRectified.isRectified_of_isQuantifierFree (.conj head suffix)
      ⟨hHeadQF, hSuffixQF⟩
    exact ⟨⟨g2nnfConjProjLeft head suffix ⟨hHeadNNF, hSuffixNNF⟩ hr ih⟩,
      ⟨g2nnfConjProjRight head suffix ⟨hHeadNNF, hSuffixNNF⟩ hr is⟩⟩
  | cons f rest ih =>
    have hfN := hFsNNF f (by simp)
    have hfQ := hFsQF f (by simp)
    have hrN : ∀ g ∈ rest, FormulaN.isNNF g := fun g hg => hFsNNF g (by simp; right; exact hg)
    have hrQ : ∀ g ∈ rest, isQuantifierFree g := fun g hg => hFsQF g (by simp; right; exact hg)
    obtain ⟨⟨left⟩, ⟨right⟩⟩ := ih f hfN hrN hfQ hrQ
    let S := listConj f (rest ++ [suffix])
    let P := listConj f rest
    have hSN : S.isNNF := (G2nnfDeductionTreeCore.allNNF left).1 S
      ((LCS.Finset.mem_singleton S S).mpr rfl)
    have hPN : P.isNNF := (G2nnfDeductionTreeCore.allNNF left).2 P
      ((LCS.Finset.mem_singleton P P).mpr rfl)
    have hSQ : isQuantifierFree S := listConj_isQuantifierFree f _ hfQ
      (by intro g hg; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
          rcases hg with hg | rfl; exact hrQ g hg; exact hSuffixQF)
    have hPQ : isQuantifierFree P := listConj_isQuantifierFree f rest hfQ hrQ
    have hSourceN : FormulaN.isNNF (.conj head S) := ⟨hHeadNNF, hSN⟩
    have hSourceR := AllRectified.isRectified_of_isQuantifierFree (.conj head S) ⟨hHeadQF, hSQ⟩
    obtain ⟨idHead⟩ := g2nnf_identity_qf (hL := hNoEq) head hHeadNNF hHeadQF
    have toHead := g2nnfConjProjLeft (hNoEq := hNoEq) head S hSourceN hSourceR idHead
    have toP : G2nnfProofTree hNoEq {FormulaN.conj head S} {P} :=
      .onePremise (.conjLeft2 head S ∅ {P}) trivial rfl
        ⟨trivial, allNNF_singletons hSourceN hPN,
          (by intro seq h; simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h
              subst seq; exact G2nnfDeductionTreeCore.allNNF left),
          allRectified_singletons hSourceR (AllRectified.isRectified_of_isQuantifierFree P hPQ)⟩ left
    have toSuffix : G2nnfProofTree hNoEq {FormulaN.conj head S} {suffix} :=
      .onePremise (.conjLeft2 head S ∅ {suffix}) trivial rfl
        ⟨trivial, allNNF_singletons hSourceN hSuffixNNF,
          (by intro seq h; simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h
              subst seq; exact G2nnfDeductionTreeCore.allNNF right),
          allRectified_singletons hSourceR (AllRectified.isRectified_of_isQuantifierFree suffix hSuffixQF)⟩ right
    refine ⟨⟨?_⟩, ⟨toSuffix⟩⟩
    exact .twoPremise (.conjRight head P {FormulaN.conj head S} ∅) trivial rfl
      ⟨trivial, allNNF_singletons hSourceN ⟨hHeadNNF, hPN⟩,
        (by intro seq h; simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with rfl | rfl
            exact G2nnfDeductionTreeCore.allNNF toHead
            exact G2nnfDeductionTreeCore.allNNF toP),
        allRectified_singletons hSourceR
          (AllRectified.isRectified_of_isQuantifierFree (.conj head P) ⟨hHeadQF, hPQ⟩)⟩ toHead toP

-- ===================================================================
-- Lemma 7.6.1 (companion theorem): g2nnfCInstanceCombinationUniversal
-- ===================================================================

-- ATTACH-BLOCKER: private name in relocated declaration
/-- Lemma 7.6.1 (companion theorem): concatenate the ordered nonempty
instantiation lists for K and Ls. Their right-associated c-instance D entails
each group, so conjunction on the right derives D -> (K and Ls). -/
theorem g2nnfCInstanceCombinationUniversal {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (x : Nat) (C : FormulaN L)
    (K Ls : FormulaN L)
    (hK : isCInstanceOf K (FormulaN.all x C))
    (hL : isCInstanceOf Ls (FormulaN.all x C)) :
    ∃ D, isCInstanceOf D (FormulaN.all x C) ∧
      Nonempty (G2nnfProofTree hNoEq
        ({D} : LCS.Finset (FormulaN L))
        ({FormulaN.conj K Ls} : LCS.Finset (FormulaN L))) := by
-- BEGIN PROOF
  obtain ⟨tK, hK₀, tsK, hsK, hGroundK, hGroundKs,
    hK₀src, hK₀wf, hKrest, hKform⟩ :=
    cinstance_all_decompose x C K hK
  obtain ⟨tL, hL₀, tsL, hsL, hGroundL, hGroundLs,
    hL₀src, hL₀wf, hLrest, hLform⟩ :=
    cinstance_all_decompose x C Ls hL
  have hGroundD :
      ∀ t ∈ tsK ++ tL :: tsL, Term.isClosed t := by
    intro t ht
    simp only [List.mem_append, List.mem_cons] at ht
    rcases ht with ht | rfl | ht
    · exact hGroundKs t ht
    · exact hGroundL
    · exact hGroundLs t ht
  let ciD : CInstance L :=
    CInstance.forallInst x C tK hK₀
      (tsK ++ tL :: tsL) (hsK ++ hL₀ :: hsL)
      hGroundK hGroundD
  have hLwhole :
      CInstance.WellFormedList x C
        (tL :: tsL) (hL₀ :: hsL) :=
    ⟨hL₀src, hL₀wf, hLrest⟩
  have hDrest :
      CInstance.WellFormedList x C
        (tsK ++ tL :: tsL) (hsK ++ hL₀ :: hsL) :=
    CInstance.WellFormedList_append x C
      tsK hsK (tL :: tsL) (hL₀ :: hsL) hKrest hLwhole
  have hDwf : CInstance.WellFormed ciD := by
    simp only [ciD, CInstance.WellFormed]
    exact ⟨hK₀src, hK₀wf, hDrest⟩
  rw [rightConj_eq_listConj] at hKform hLform
  have hDform : ciD.toFormula =
      listConj hK₀.toFormula (hsK.map CInstance.toFormula ++ [Ls]) := by
    simp only [ciD, CInstance.toFormula, rightConj_eq_listConj,
      List.map_append, List.map_cons]
    rw [listConj_suffix, hLform]
  have hKN := isCInstanceOf_isNNF K (.all x C) hK
  have hLN := isCInstanceOf_isNNF Ls (.all x C) hL
  have hKQ := isCInstanceOf_isQuantifierFree K (.all x C) hK
  have hLQ := isCInstanceOf_isQuantifierFree Ls (.all x C) hL
  obtain ⟨⟨left⟩, ⟨right⟩⟩ := g2nnf_right_conj_split (hNoEq := hNoEq)
    (hsK.map CInstance.toFormula) hK₀.toFormula Ls
    (cInstance_toFormula_isNNF hK₀) hLN
    (by intro f hf; rcases List.mem_map.mp hf with ⟨ci, _, rfl⟩
        exact cInstance_toFormula_isNNF ci)
    (CInstance.isQuantifierFree hK₀) hLQ
    (by intro f hf; rcases List.mem_map.mp hf with ⟨ci, _, rfl⟩
        exact CInstance.isQuantifierFree ci)
  rw [hKform, ← hDform] at left
  rw [← hDform] at right
  refine ⟨ciD.toFormula, ⟨ciD, rfl, rfl, hDwf⟩, ⟨?_⟩⟩
  exact .twoPremise (.conjRight K Ls {ciD.toFormula} ∅) trivial rfl
    ⟨trivial, allNNF_singletons (cInstance_toFormula_isNNF ciD) ⟨hKN, hLN⟩,
      (by intro seq h; simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl
          exact G2nnfDeductionTreeCore.allNNF left
          exact G2nnfDeductionTreeCore.allNNF right),
      allRectified_singletons
        (AllRectified.isRectified_of_isQuantifierFree _ (CInstance.isQuantifierFree ciD))
        (AllRectified.isRectified_of_isQuantifierFree _ ⟨hKQ, hLQ⟩)⟩ left right

-- ===================================================================
-- Lemma 7.6.1: g2nnfCInstanceCombination
-- ===================================================================

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.LowerConstruction
/-- Lemma 7.6.1: Let A be a sentence in NNF and in Skolem normal form. For any two c-instances K and L of A, there exists a c-instance D of A such that the sequent D -> (K and L) is provable. That is, the set of c-instances is closed under combination: given any two c-instances, a single c-instance that subsumes both can be constructed. The proof proceeds by structural induction on the NNF Skolem formula A. Case (i) literal: K = L = A, take D = A. Case (ii) binary connective: decompose K and L, apply the induction hypothesis, combine as D = (D_1 * D_2). Case (iii) universal quantifier: concatenate the instantiation lists and derive the grouped conjunction. -/
theorem g2nnfCInstanceCombination {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (B : FormulaN L)
    (hNNF : FormulaN.isNNF B)
    (hSkolem : isSkolemNormalForm B)
    (K Ls : FormulaN L)
    (hK : isCInstanceOf K B)
    (hL : isCInstanceOf Ls B) :
    ∃ D, isCInstanceOf D B ∧
      Nonempty (G2nnfProofTree hNoEq
        ({D} : LCS.Finset (FormulaN L))
        ({FormulaN.conj K Ls} : LCS.Finset (FormulaN L))) := by
-- BEGIN PROOF
  have literalCase (A : FormulaN L)
      (hLit : A.isAtomic ∨ ∃ F, A = .neg F ∧ F.isAtomic)
      (_hAN : A.isNNF) (K Ls : FormulaN L)
      (hK : isCInstanceOf K A) (hLs : isCInstanceOf Ls A) :
      ∃ D, isCInstanceOf D A ∧ Nonempty (G2nnfProofTree hNoEq {D} {FormulaN.conj K Ls}) := by
    exact g2nnfCInstanceCombinationLiteral A hLit K Ls hK hLs
  have hShape : isSkolemNormalFormShape B := hSkolem.1
  clear hSkolem
  induction B generalizing K Ls with
  | predN P args =>
      exact literalCase
        (.predN P args) (Or.inl rfl) hNNF K Ls hK hL
  | eq_ hEq t₁ t₂ =>
      exact literalCase
        (.eq_ hEq t₁ t₂) (Or.inl rfl) hNNF K Ls hK hL
  | neg A =>
      exact literalCase
        (.neg A) (Or.inr ⟨A, rfl, hShape⟩) hNNF K Ls hK hL
  | conj B C ihB ihC =>
      exact g2nnfCInstanceCombinationConnective (hNoEq := hNoEq) B C true
        (fun K' Ls' hK' hL' =>
          ihB hNNF.1 K' Ls' hK' hL' hShape.1)
        (fun K' Ls' hK' hL' =>
          ihC hNNF.2 K' Ls' hK' hL' hShape.2)
        (.conj B C) rfl K Ls hK hL
  | disj B C ihB ihC =>
      exact g2nnfCInstanceCombinationConnective (hNoEq := hNoEq) B C false
        (fun K' Ls' hK' hL' =>
          ihB hNNF.1 K' Ls' hK' hL' hShape.1)
        (fun K' Ls' hK' hL' =>
          ihC hNNF.2 K' Ls' hK' hL' hShape.2)
        (.disj B C) rfl K Ls hK hL
  | impl B C ihB ihC =>
      exact hNNF.elim
  | all x C ih =>
      exact g2nnfCInstanceCombinationUniversal (hNoEq := hNoEq) x C K Ls hK hL
  | ex x C ih =>
      exact hShape.elim



/-- Lemma 7.6.1, connective case: combine the two component witnesses
using induction hypotheses in the same G1 calculus as the conclusion.
The language branches are separate, with the equality branch in G1nnf=. -/
theorem cInstance_combination_connective {L : Language}
    [DecidableEq (FormulaN L)]
    (B C : FormulaN L) (isConj : Bool)
    (A : FormulaN L)
    (hA : A = if isConj then FormulaN.conj B C else FormulaN.disj B C)
    (K Ls : FormulaN L)
    (hK : isCInstanceOf K A) (hL : isCInstanceOf Ls A) :
    (∀ hNoEq : L.withoutEquality,
      (∀ K' Ls', isCInstanceOf K' B → isCInstanceOf Ls' B →
        ∃ D, isCInstanceOf D B ∧
          Nonempty (G1nnfProofTree hNoEq
            ({D} : LCS.Finset (FormulaN L))
            ({FormulaN.conj K' Ls'} : LCS.Finset (FormulaN L)))) →
      (∀ K' Ls', isCInstanceOf K' C → isCInstanceOf Ls' C →
        ∃ D, isCInstanceOf D C ∧
          Nonempty (G1nnfProofTree hNoEq
            ({D} : LCS.Finset (FormulaN L))
            ({FormulaN.conj K' Ls'} : LCS.Finset (FormulaN L)))) →
      ∃ D, isCInstanceOf D A ∧
        Nonempty (G1nnfProofTree hNoEq
          ({D} : LCS.Finset (FormulaN L))
          ({FormulaN.conj K Ls} : LCS.Finset (FormulaN L)))) ∧
    (∀ hEq : L.hasEquality = true,
      (∀ K' Ls', isCInstanceOf K' B → isCInstanceOf Ls' B →
        ∃ D, isCInstanceOf D B ∧
          Nonempty (LCS.CutElim.Hauptsatz.Equality.G1nnfEqProofTree hEq
            ({D} : LCS.Finset (FormulaN L))
            ({FormulaN.conj K' Ls'} : LCS.Finset (FormulaN L)))) →
      (∀ K' Ls', isCInstanceOf K' C → isCInstanceOf Ls' C →
        ∃ D, isCInstanceOf D C ∧
          Nonempty (LCS.CutElim.Hauptsatz.Equality.G1nnfEqProofTree hEq
            ({D} : LCS.Finset (FormulaN L))
            ({FormulaN.conj K' Ls'} : LCS.Finset (FormulaN L)))) →
      ∃ D, isCInstanceOf D A ∧
        Nonempty (LCS.CutElim.Hauptsatz.Equality.G1nnfEqProofTree hEq
          ({D} : LCS.Finset (FormulaN L))
          ({FormulaN.conj K Ls} : LCS.Finset (FormulaN L)))) := by
  -- REPAIR(T7-79): proof pending (G1nnf/G1nnf= connective combination).
  sorry

/-- Lemma 7.6.1, universal case: concatenate the ordered nonempty
instantiation families. The right-nested resulting c-instance implies the
grouped conjunction in G1nnf or G1nnf= for the respective language branch. -/
theorem cInstance_combination_universal {L : Language}
    [DecidableEq (FormulaN L)]
    (x : Nat) (C : FormulaN L) (K Ls : FormulaN L)
    (hK : isCInstanceOf K (FormulaN.all x C))
    (hL : isCInstanceOf Ls (FormulaN.all x C)) :
    (∀ hNoEq : L.withoutEquality,
      ∃ D, isCInstanceOf D (FormulaN.all x C) ∧
        Nonempty (G1nnfProofTree hNoEq
          ({D} : LCS.Finset (FormulaN L))
          ({FormulaN.conj K Ls} : LCS.Finset (FormulaN L)))) ∧
    (∀ hEq : L.hasEquality = true,
      ∃ D, isCInstanceOf D (FormulaN.all x C) ∧
        Nonempty (LCS.CutElim.Hauptsatz.Equality.G1nnfEqProofTree hEq
          ({D} : LCS.Finset (FormulaN L))
          ({FormulaN.conj K Ls} : LCS.Finset (FormulaN L)))) := by
  -- REPAIR(T7-79): proof pending (G1nnf/G1nnf= universal combination).
  sorry

/-- Lemma 7.6.1, existence assertion: for any two c-instances K and Ls
of an NNF Skolem-normal sentence B, a c-instance D proves D -> (K and Ls)
in G1nnf when the language has no equality, and in G1nnf= when it does.
The same repaired c-instance relation is used in both branches. The
computable combination realization is deferred under OD-A17. -/
@[blueprint "chap7__lemma_7_6_1" (main := true)]
theorem cInstance_combination {L : Language}
    [DecidableEq (FormulaN L)]
    (B : FormulaN L) (hNNF : FormulaN.isNNF B)
    (hSkolem : isSkolemNormalForm B)
    (K Ls : FormulaN L)
    (hK : isCInstanceOf K B) (hL : isCInstanceOf Ls B) :
    (∀ hNoEq : L.withoutEquality,
      ∃ D, isCInstanceOf D B ∧
        Nonempty (G1nnfProofTree hNoEq
          ({D} : LCS.Finset (FormulaN L))
          ({FormulaN.conj K Ls} : LCS.Finset (FormulaN L)))) ∧
    (∀ hEq : L.hasEquality = true,
      ∃ D, isCInstanceOf D B ∧
        Nonempty (LCS.CutElim.Hauptsatz.Equality.G1nnfEqProofTree hEq
          ({D} : LCS.Finset (FormulaN L))
          ({FormulaN.conj K Ls} : LCS.Finset (FormulaN L)))) 

-- ===================================================================
-- Lemma 7.6.2 (companion theorem): midsequentCInstancesProvable
-- ===================================================================







-- ===================================================================
-- Lemma 7.6.2 (companion theorem): cInstanceConjunctionAntecedent
-- ===================================================================

-- ATTACH-BLOCKER: private name in relocated declaration
/-- Lemma 7.6.2 (companion theorem): A nonempty antecedent of
c-instances can be collapsed to their conjunction without leaving
NNF. From `head, tail →` this derives `listConj head tail →`.
The c-instance hypotheses provide the quantifier-free NNF identities
needed by the cut-based collapse. -/
theorem cInstanceConjunctionAntecedent {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (B head : FormulaN L)
    (tail : List (FormulaN L))
    (_hHead : isCInstanceOf head B)
    (_hTail : ∀ C, C ∈ tail → isCInstanceOf C B)
    (_hProv : Nonempty (G2nnfProofTree hNoEq
      (LCS.Finset.ofList (head :: tail))
      (∅ : LCS.Finset (FormulaN L)))) :
    Nonempty (G2nnfProofTree hNoEq
      ({listConj head tail} : LCS.Finset (FormulaN L))
      (∅ : LCS.Finset (FormulaN L))) := by
-- BEGIN PROOF
  have hAll :
      ∀ C, C ∈ head :: tail → isCInstanceOf C B := by
    intro C hC
    rcases List.mem_cons.mp hC with hC | hC
    · subst C
      exact _hHead
    · exact _hTail C hC
  have projects :
      ∀ (a : FormulaN L) (xs : List (FormulaN L)),
        (∀ C, C ∈ a :: xs → isCInstanceOf C B) →
        ∀ C, C ∈ a :: xs →
          Nonempty (G2nnfProofTree hNoEq
            ({listConj a xs} : LCS.Finset (FormulaN L))
            ({C} : LCS.Finset (FormulaN L))) := by
    intro a xs
    induction xs generalizing a with
    | nil =>
        intro hCI C hC
        have hCa : C = a := List.mem_singleton.mp hC
        subst C
        exact g2nnf_identity_qf (hL := hNoEq) a
          (isCInstanceOf_isNNF a B (hCI a List.mem_cons_self))
          (isCInstanceOf_isQuantifierFree a B
            (hCI a List.mem_cons_self))
    | cons next rest ih =>
        intro hCI C hC
        have hListQF :
            isQuantifierFree (listConj a (next :: rest)) :=
          listConj_isQuantifierFree a (next :: rest)
            (isCInstanceOf_isQuantifierFree a B
              (hCI a List.mem_cons_self))
            (fun f hf =>
              isCInstanceOf_isQuantifierFree f B
                (hCI f (List.mem_cons.mpr (Or.inr hf))))
        have hListNNF : FormulaN.isNNF (listConj a (next :: rest)) := by
          rw [← rightConj_eq_listConj]
          exact nnf_right_conj_local _ a
            (isCInstanceOf_isNNF a B (hCI a List.mem_cons_self))
            (fun f hf => isCInstanceOf_isNNF f B
              (hCI f (List.mem_cons.mpr (Or.inr hf))))
        have hListRect :
            isRectified (listConj a (next :: rest)) :=
          AllRectified.isRectified_of_isQuantifierFree _ hListQF
        rcases List.mem_cons.mp hC with hCa | hC
        · subst C
          obtain ⟨idA⟩ := g2nnf_identity_qf (hL := hNoEq) a
            (isCInstanceOf_isNNF a B (hCI a List.mem_cons_self))
            (isCInstanceOf_isQuantifierFree a B
              (hCI a List.mem_cons_self))
          exact ⟨G2nnfDeductionTreeCore.onePremise
            (.conjLeft1 a (listConj next rest) ∅ {a}) trivial rfl
            ⟨trivial, allNNF_singletons hListNNF ((G2nnfDeductionTreeCore.allNNF idA).2 a
                ((LCS.Finset.mem_singleton a a).mpr rfl)),
              (by intro seq h
                  simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h
                  subst seq; exact G2nnfDeductionTreeCore.allNNF idA),
              allRectified_singletons hListRect
              (AllRectified.isRectified_of_isQuantifierFree a
                (isCInstanceOf_isQuantifierFree a B
                  (hCI a List.mem_cons_self)))⟩
            idA⟩
        · obtain ⟨tailTree⟩ :=
            ih next
              (fun E hE =>
                hCI E (List.mem_cons.mpr (Or.inr hE)))
              C hC
          exact ⟨G2nnfDeductionTreeCore.onePremise
            (.conjLeft2 a (listConj next rest) ∅ {C}) trivial rfl
            ⟨trivial, allNNF_singletons hListNNF ((G2nnfDeductionTreeCore.allNNF tailTree).2 C
                ((LCS.Finset.mem_singleton C C).mpr rfl)),
              (by intro seq h
                  simp only [G2nnfRuleCore.premises, List.mem_cons, List.not_mem_nil, or_false] at h
                  subst seq; exact G2nnfDeductionTreeCore.allNNF tailTree),
              allRectified_singletons hListRect
              (tailTree.allRectified.2 C
                ((LCS.Finset.mem_singleton C C).mpr rfl))⟩
            tailTree⟩
  have insertEmptySingleton (A : FormulaN L) :
      LCS.Finset.insert A
          (∅ : LCS.Finset (FormulaN L)) =
        ({A} : LCS.Finset (FormulaN L)) := by
    apply LCS.Finset.ext
    intro C
    constructor
    · intro h
      apply (LCS.Finset.mem_singleton C A).mpr
      rcases LCS.Finset.mem_insert.mp h with hCA | hEmpty
      · exact hCA
      · exact (LCS.Finset.not_mem_empty hEmpty).elim
    · intro h
      apply LCS.Finset.mem_insert.mpr
      exact Or.inl ((LCS.Finset.mem_singleton C A).mp h)
  have ofListConsContext
      (H A : FormulaN L) (xs : List (FormulaN L)) :
      LCS.Finset.insert H (LCS.Finset.ofList (A :: xs)) =
        LCS.Finset.insert A
          (LCS.Finset.insert H (LCS.Finset.ofList xs)) := by
    apply LCS.Finset.ext
    intro C
    rw [LCS.Finset.mem_insert, LCS.Finset.mem_ofList,
      List.mem_cons, LCS.Finset.mem_insert,
      LCS.Finset.mem_insert, LCS.Finset.mem_ofList]
    constructor
    · intro h
      rcases h with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · intro h
      rcases h with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  have eliminate :
      ∀ (H : FormulaN L) (xs : List (FormulaN L)),
        (∀ C, C ∈ xs →
          Nonempty (G2nnfProofTree hNoEq
            ({H} : LCS.Finset (FormulaN L))
            ({C} : LCS.Finset (FormulaN L)))) →
        Nonempty (G2nnfProofTree hNoEq
          (LCS.Finset.insert H (LCS.Finset.ofList xs))
          (∅ : LCS.Finset (FormulaN L))) →
        Nonempty (G2nnfProofTree hNoEq
          ({H} : LCS.Finset (FormulaN L))
          (∅ : LCS.Finset (FormulaN L))) := by
    intro H xs
    induction xs with
    | nil =>
        intro _ hTree
        change Nonempty (G2nnfProofTree hNoEq
          (LCS.Finset.insert H
            (∅ : LCS.Finset (FormulaN L)))
          (∅ : LCS.Finset (FormulaN L))) at hTree
        rw [insertEmptySingleton] at hTree
        exact hTree
    | cons A rest ih =>
        intro hProjects hTree
        obtain ⟨currentTree⟩ := hTree
        obtain ⟨projection⟩ :=
          hProjects A List.mem_cons_self
        have projectionForCut : G2nnfProofTree hNoEq
            ({H} : G2FormulaFinset) (LCS.Finset.insert A (∅ : G2FormulaFinset)) := by
          rw [insertEmptySingleton]
          exact projection
        have currentForCut :
            G2nnfProofTree hNoEq
              (LCS.Finset.insert A
                (LCS.Finset.insert H
                  (LCS.Finset.ofList rest)))
              (∅ : LCS.Finset (FormulaN L)) := by
          rw [← ofListConsContext H A rest]
          exact currentTree
        have cutTree :
            G2nnfProofTree hNoEq
              (LCS.Finset.insert H
                (LCS.Finset.ofList rest))
              (∅ : LCS.Finset (FormulaN L)) := by
          have cut := g2nnfCut (hL := hNoEq) A projectionForCut currentForCut
          have hAnte : LCS.Finset.union ({H} : G2FormulaFinset)
              (LCS.Finset.insert H (LCS.Finset.ofList rest)) =
              LCS.Finset.insert H (LCS.Finset.ofList rest) := by
            apply LCS.Finset.ext
            intro F
            constructor
            · intro h
              rcases LCS.Finset.mem_union.mp h with h | h
              · exact LCS.Finset.mem_insert.mpr
                  (Or.inl ((LCS.Finset.mem_singleton F H).mp h))
              · exact h
            · intro h
              exact LCS.Finset.mem_union.mpr (Or.inr h)
          have hSucc : LCS.Finset.union (∅ : LCS.Finset (FormulaN L))
              (∅ : LCS.Finset (FormulaN L)) = (∅ : LCS.Finset (FormulaN L)) := by
            apply LCS.Finset.ext
            intro F
            simp [LCS.Finset.mem_empty]
          rw [hAnte, hSucc] at cut
          exact cut
        apply ih
        · intro C hC
          exact hProjects C
            (List.mem_cons.mpr (Or.inr hC))
        · exact ⟨cutTree⟩
  obtain ⟨sourceTree⟩ := _hProv
  have hListConjQF : isQuantifierFree (listConj head tail) :=
    listConj_isQuantifierFree head tail
      (isCInstanceOf_isQuantifierFree head B _hHead)
      (fun C hC =>
        isCInstanceOf_isQuantifierFree C B (_hTail C hC))
  exact eliminate (listConj head tail) (head :: tail)
    (projects head tail hAll)
    ⟨g2nnfWeakLeft (hL := hNoEq) (listConj head tail)
      (by rw [← rightConj_eq_listConj]
          exact nnf_right_conj_local _ head (isCInstanceOf_isNNF head B _hHead)
            (fun C hC => isCInstanceOf_isNNF C B (_hTail C hC)))
      (AllRectified.isRectified_of_isQuantifierFree _
        hListConjQF)
      sourceTree⟩

-- ===================================================================
-- Helper: Every NNF Skolem formula has at least one c-instance
-- ===================================================================

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.LowerConstruction
/-- Substituting a term preserves the structural Skolem-normal-form
shape.  In particular, substitution cannot introduce an existential,
an implication, or a non-atomic negand. -/
theorem isSkolemNormalFormShape_formulaSubstN {L : Language}
    (B : FormulaN L) (t : Term L) (x : Nat)
    (hShape : isSkolemNormalFormShape B) :
    isSkolemNormalFormShape (formulaSubstN B t x) := by
  induction B with
  | predN _ _ =>
      exact trivial
  | eq_ _ _ _ =>
      exact trivial
  | neg A _ =>
      exact isAtomic_formulaSubstN A t x hShape
  | conj A B ihA ihB =>
      exact ⟨ihA hShape.1, ihB hShape.2⟩
  | disj A B ihA ihB =>
      exact ⟨ihA hShape.1, ihB hShape.2⟩
  | impl _ _ _ _ =>
      exact hShape.elim
  | all y B ih =>
      simp only [formulaSubstN]
      split
      · exact ih hShape
      · exact hShape
  | ex _ _ _ =>
      exact hShape.elim

-- ATTACH-BLOCKER: private declaration
/-- A maximal quantified occurrence selected inside a structurally
Skolem formula has the same structural Skolem shape. -/
private theorem isSkolemNormalFormShape_selected
    {L : Language} {A : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A)
    (hShape : isSkolemNormalFormShape A) :
    isSkolemNormalFormShape occurrence.selected := by
  induction occurrence with
  | all _ _ =>
      exact hShape
  | ex _ _ =>
      exact hShape
  | conjLeft _ _ ih =>
      exact ih hShape.1
  | conjRight _ _ ih =>
      exact ih hShape.2
  | disjLeft _ _ ih =>
      exact ih hShape.1
  | disjRight _ _ ih =>
      exact ih hShape.2

-- ATTACH-BLOCKER: private declaration
/-- Replacing one exact maximal occurrence by another structurally
Skolem formula preserves the ambient structural shape. -/
private theorem isSkolemNormalFormShape_replace
    {L : Language} {A : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A)
    (replacement : FormulaN L)
    (hShape : isSkolemNormalFormShape A)
    (hReplacement :
      isSkolemNormalFormShape replacement) :
    isSkolemNormalFormShape
      (occurrence.replace replacement) := by
  induction occurrence with
  | all _ _ =>
      exact hReplacement
  | ex _ _ =>
      exact hReplacement
  | conjLeft occurrence B ih =>
      exact ⟨ih hShape.1, hShape.2⟩
  | conjRight A occurrence ih =>
      exact ⟨hShape.1, ih hShape.2⟩
  | disjLeft occurrence B ih =>
      exact ⟨ih hShape.1, hShape.2⟩
  | disjRight A occurrence ih =>
      exact ⟨hShape.1, ih hShape.2⟩

-- ATTACH-BLOCKER: unsupported untagged abbrev
/-- A term paired with evidence that it has no free variables. -/
abbrev ClosedTerm (L : Language) :=
  {t : Term L // Term.isClosed t}

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Binary congruence, kept local because the core environment used by
this book exposes unary `congrArg` but no `congrArg₂` helper. -/
theorem congrArg₂_local {α β γ : Type}
    (f : α → β → γ) {a₁ a₂ : α} {b₁ b₂ : β}
    (ha : a₁ = a₂) (hb : b₁ = b₂) :
    f a₁ b₁ = f a₂ b₂ := by
  cases ha
  cases hb
  rfl

-- ATTACH-BLOCKER: unsupported untagged structure
/-- A partial map from proof eigenvariables to already-closed terms.
The chronological lower-path fold extends this map only after the
corresponding exact existential-left occurrence is crossed. -/
structure ClosedEigenvarMap (L : Language) where
  lookup : Nat → Option (ClosedTerm L)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
def ClosedEigenvarMap.empty {L : Language} :
    ClosedEigenvarMap L :=
  ⟨fun _ => none⟩

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
def ClosedEigenvarMap.insert {L : Language}
    (eigenMap : ClosedEigenvarMap L) (x : Nat)
    (t : ClosedTerm L) : ClosedEigenvarMap L :=
  ⟨fun y => if y = x then some t else eigenMap.lookup y⟩

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
theorem ClosedEigenvarMap.lookup_insert_self
    {L : Language} (eigenMap : ClosedEigenvarMap L)
    (x : Nat) (t : ClosedTerm L) :
    (eigenMap.insert x t).lookup x = some t := by
  simp [ClosedEigenvarMap.insert]

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
theorem ClosedEigenvarMap.lookup_insert_of_ne
    {L : Language} (eigenMap : ClosedEigenvarMap L)
    (x y : Nat) (t : ClosedTerm L) (hyx : y ≠ x) :
    (eigenMap.insert x t).lookup y = eigenMap.lookup y := by
  simp [ClosedEigenvarMap.insert, hyx]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Close every unprotected variable using the current eigenvariable
map, with the supplied seed as the explicit fallback.  Variables in
`bound` are binder-protected and remain variables. -/
def closeBaseTermAt {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (bound : List Nat) : Term L → Term L
  | .var x =>
      if x ∈ bound then
        .var x
      else
        match eigenMap.lookup x with
        | some t => t.1
        | none => seed.1
  | .const c => .const c
  | .func f ts =>
      .func f (fun i =>
        closeBaseTermAt seed eigenMap bound (ts i))

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.ClosedSubstitution, LCS.Herbrand.SHGTheorem.Herbrand.Provenance, LCS.Herbrand.SHGTheorem.Herbrand.ScopeAndPurity
/-- Close a standalone Skolem-language term with the current
chronological eigenvariable map and the explicit seed fallback. -/
def closeSkolemTermWithSeed {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (t : Term L) : Term L :=
  closeBaseTermAt seed eigenMap [] t

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.ClosedSubstitution
/-- Every variable retained by term normalization is protected by
the enclosing binder list. -/
theorem closeBaseTermAt_fv_bound {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (bound : List Nat) (t : Term L) :
    ∀ y, y ∈ termFV (closeBaseTermAt seed eigenMap bound t) →
      y ∈ bound := by
  induction t with
  | var x =>
      intro y hy
      by_cases hx : x ∈ bound
      · have hyx : y = x := by
          simpa [closeBaseTermAt, hx, termFV] using hy
        simpa [hyx] using hx
      · cases hMap : eigenMap.lookup x with
        | none =>
            have hClosed := seed.2
            unfold Term.isClosed at hClosed
            simp only [closeBaseTermAt, if_neg hx, hMap] at hy
            rw [hClosed] at hy
            exact hy.elim
        | some t =>
            have hClosed := t.2
            unfold Term.isClosed at hClosed
            simp only [closeBaseTermAt, if_neg hx, hMap] at hy
            rw [hClosed] at hy
            exact hy.elim
  | const _ =>
      intro y hy
      exact hy.elim
  | func f ts ih =>
      intro y hy
      simp only [closeBaseTermAt, termFV] at hy
      obtain ⟨i, hi⟩ := hy
      exact ih i y hi

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.ClosedSubstitution
/-- Normalization never introduces a variable absent from the source
term; it only removes unprotected variables. -/
theorem closeBaseTermAt_fv_source {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (bound : List Nat) (t : Term L) :
    ∀ y, y ∈ termFV (closeBaseTermAt seed eigenMap bound t) →
      y ∈ termFV t := by
  induction t with
  | var x =>
      intro y hy
      by_cases hx : x ∈ bound
      · have hyx : y = x := by
          simpa [closeBaseTermAt, hx, termFV] using hy
        simpa [termFV, hyx]
      · cases hMap : eigenMap.lookup x with
        | none =>
            have hClosed := seed.2
            unfold Term.isClosed at hClosed
            simp only [closeBaseTermAt, if_neg hx, hMap] at hy
            rw [hClosed] at hy
            exact hy.elim
        | some t =>
            have hClosed := t.2
            unfold Term.isClosed at hClosed
            simp only [closeBaseTermAt, if_neg hx, hMap] at hy
            rw [hClosed] at hy
            exact hy.elim
  | const _ =>
      intro y hy
      exact hy.elim
  | func f ts ih =>
      intro y hy
      simp only [closeBaseTermAt, termFV] at hy
      obtain ⟨i, hi⟩ := hy
      exact ⟨i, ih i y hi⟩

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.Provenance, LCS.Herbrand.SHGTheorem.Herbrand.ScopeAndPurity
/-- Standalone term normalization is closed. -/
theorem closeSkolemTermWithSeed_isClosed {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (t : Term L) :
    Term.isClosed (closeSkolemTermWithSeed seed eigenMap t) := by
  unfold Term.isClosed closeSkolemTermWithSeed
  ext y
  constructor
  · intro hy
    have hBound :=
      closeBaseTermAt_fv_bound seed eigenMap [] t y hy
    exact (List.not_mem_nil hBound).elim
  · intro hy
    exact hy.elim

-- ATTACH-BLOCKER: private declaration
/-- The protected-variable list is extensional: only membership
matters, not order or multiplicity. -/
private theorem closeBaseTermAt_congr {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (bound₁ bound₂ : List Nat)
    (hBound : ∀ x, x ∈ bound₁ ↔ x ∈ bound₂)
    (t : Term L) :
    closeBaseTermAt seed eigenMap bound₁ t =
      closeBaseTermAt seed eigenMap bound₂ t := by
  induction t with
  | var x =>
      simp only [closeBaseTermAt]
      by_cases hx : x ∈ bound₁
      · rw [if_pos hx, if_pos ((hBound x).mp hx)]
      · rw [if_neg hx,
          if_neg (fun h => hx ((hBound x).mpr h))]
  | const _ =>
      rfl
  | func f ts ih =>
      simp only [closeBaseTermAt, Term.func.injEq,
        heq_eq_eq, true_and]
      funext i
      exact ih i

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.ClosedSubstitution
/-- A term whose variables are all protected is fixed by
normalization. -/
theorem closeBaseTermAt_eq_self {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (bound : List Nat) (t : Term L)
    (hBound : ∀ x, x ∈ termFV t → x ∈ bound) :
    closeBaseTermAt seed eigenMap bound t = t := by
  induction t with
  | var x =>
      have hx : x ∈ bound :=
        hBound x (by simp [termFV])
      simp [closeBaseTermAt, hx]
  | const _ =>
      rfl
  | func f ts ih =>
      simp only [closeBaseTermAt, Term.func.injEq,
        heq_eq_eq, true_and]
      funext i
      apply ih i
      intro x hx
      apply hBound x
      exact ⟨i, hx⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Capture-aware formula normalization: bound variables are
protected while every genuinely free variable is closed through the
current eigenvariable map or the seed fallback. -/
def closeFormulaAt {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (bound : List Nat) : FormulaN L → FormulaN L
  | .predN P ts =>
      .predN P (fun i =>
        closeBaseTermAt seed eigenMap bound (ts i))
  | .eq_ hEq lhs rhs =>
      .eq_ hEq
        (closeBaseTermAt seed eigenMap bound lhs)
        (closeBaseTermAt seed eigenMap bound rhs)
  | .neg A =>
      .neg (closeFormulaAt seed eigenMap bound A)
  | .conj A B =>
      .conj (closeFormulaAt seed eigenMap bound A)
        (closeFormulaAt seed eigenMap bound B)
  | .disj A B =>
      .disj (closeFormulaAt seed eigenMap bound A)
        (closeFormulaAt seed eigenMap bound B)
  | .impl A B =>
      .impl (closeFormulaAt seed eigenMap bound A)
        (closeFormulaAt seed eigenMap bound B)
  | .all x A =>
      .all x (closeFormulaAt seed eigenMap (x :: bound) A)
  | .ex x A =>
      .ex x (closeFormulaAt seed eigenMap (x :: bound) A)

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.ClosedSubstitution
/-- Close every free variable of a formula. -/
def closeFormula {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (A : FormulaN L) : FormulaN L :=
  closeFormulaAt seed eigenMap [] A

-- ATTACH-BLOCKER: private name in relocated declaration
/-- Formula normalization has the same extensional binder protection
as term normalization. -/
theorem closeFormulaAt_congr {L : Language}
    (seed : ClosedTerm L) (eigenMap : ClosedEigenvarMap L)
    (bound₁ bound₂ : List Nat)
    (hBound : ∀ x, x ∈ bound₁ ↔ x ∈ bound₂)
    (A : FormulaN L) :
    closeFormulaAt seed eigenMap bound₁ A =
      closeFormulaAt seed eigenMap bound₂ A := by
  induction A generalizing bound₁ bound₂ with
  | predN P ts =>
      simp only [closeFormulaAt, FormulaN.predN.injEq,
        heq_eq_eq, true_and]
      funext i
      exact closeBaseTermAt_congr
        seed eigenMap bound₁ bound₂ hBound (ts i)
  | eq_ hEq lhs rhs =>
      simp only [closeFormulaAt, FormulaN.eq_.injEq,
        heq_eq_eq, true_and]
      exact
        ⟨closeBaseTermAt_congr
            seed eigenMap bound₁ bound₂ hBound lhs,
          closeBaseTermAt_congr
            seed eigenMap bound₁ bound₂ hBound rhs⟩
  | neg A ih =>
      exact congrArg FormulaN.neg
        (ih bound₁ bound₂ hBound)
  | conj A B ihA ihB =>
      exact congrArg₂_local FormulaN.conj
        (ihA bound₁ bound₂ hBound)
        (ihB bound₁ bound₂ hBound)
  | disj A B ihA ihB =>
      exact congrArg₂_local FormulaN.disj
        (ihA bound₁ bound₂ hBound)
        (ihB bound₁ bound₂ hBound)
  | impl A B ihA ihB =>
      exact congrArg₂_local FormulaN.impl
        (ihA bound₁ bound₂ hBound)
        (ihB bound₁ bound₂ hBound)
  | all x A ih =>
      apply congrArg (FormulaN.all x)
      apply ih
      intro y
      simp only [List.mem_cons]
      exact or_congr Iff.rfl (hBound y)
  | ex x A ih =>
      apply congrArg (FormulaN.ex x)
      apply ih
      intro y
      simp only [List.mem_cons]
      exact or_congr Iff.rfl (hBound y)

end LCS.Herbrand.SHGTheorem.Herbrand
end

