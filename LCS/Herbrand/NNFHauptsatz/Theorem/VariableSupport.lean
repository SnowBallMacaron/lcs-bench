import LCS.Item
import LCS.Util
import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.NNFHauptsatz.Renaming
import LCS.Herbrand.NNFHauptsatz.Soundness
import LCS.Herbrand.SharpenedHauptsatz
import LCS.Herbrand.SharpenedHauptsatz.Permutability
import LCS.Herbrand.SharpenedHauptsatz.Theorem
import LCS.Herbrand.PrenexForm
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination
import Attach
import LCS.Herbrand.NNFHauptsatz.Theorem.VariableSupport.ProofsStamp

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Soundness
open LCS.Herbrand.SharpenedHauptsatz
open LCS.Herbrand.SharpenedHauptsatz.Permutability
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.Herbrand.PrenexForm
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
open LCS.CutElim.LK
namespace LCS.Herbrand.NNFHauptsatz.G2nnfRuleCore

/-- Lemma 7.4.2 (companion def): Extract the cut formula from a G2nnf rule,
if the rule is a cut. Returns none for non-cut rules. -/
@[blueprint "chap7__definition_7_4_4"]
def cutFormula {L : Language} : G2nnfRuleCore L → Option (FormulaN L)
  | .cut A _ _ _ _ => some A
  | _ => none

-- ===================================================================
-- Lemma 7.4.2 (required def): G2nnfRuleCore.isQuantifierRule
-- ===================================================================

/-- Lemma 7.4.2 (required def): Returns True for the four quantifier-for-subformulae rules of G2nnf (allSubLeft, allSubRight, exSubLeft, exSubRight). Returns False for all other rules. -/
@[blueprint "chap7__definition_7_4_4"]
def isQuantifierRule {L : Language} : G2nnfRuleCore L → Prop
  | .allSubLeft _ _ _ _ _ _ _ _ => True
  | .allSubRight _ _ _ _ _ _ _ _ => True
  | .exSubLeft _ _ _ _ _ _ _ _ => True
  | .exSubRight _ _ _ _ _ _ _ _ => True
  | _ => False

-- ===================================================================
-- Lemma 7.4.2 (required def): G2nnfRuleCore.isPropositionalRule
-- ===================================================================

/-- Lemma 7.4.2 (required def): Returns True for the propositional logical rules of G2nnf (conjLeft1, conjLeft2, conjRight, disjLeft, disjRight1, disjRight2). Returns False for all other rules. -/
@[blueprint "chap7__lemma_7_4_2"]
def isPropositionalRule {L : Language} :
    G2nnfRuleCore L → Prop
  | .conjLeft1 _ _ _ _ => True
  | .conjLeft2 _ _ _ _ => True
  | .conjRight _ _ _ _ => True
  | .disjLeft _ _ _ _ => True
  | .disjRight1 _ _ _ _ => True
  | .disjRight2 _ _ _ _ => True
  | _ => False

-- ===================================================================
-- Lemma 7.4.2 (required def): G2nnfRuleCore.isWeakening
-- ===================================================================

/-- Lemma 7.4.2 (required def): Returns True for weakLeft and
weakRight. Returns False for all other rules. -/
@[blueprint "chap7__definition_7_4_4"]
def isWeakening {L : Language} : G2nnfRuleCore L → Prop
  | .weakLeft _ _ _ => True
  | .weakRight _ _ _ => True
  | _ => False

-- ===================================================================
-- Lemma 7.4.2 (helper): G2nnfRuleCore.isQuantifierRuleBool
-- ===================================================================

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Theorem 7.4.1 (companion def): Returns true if a G2nnf rule is a quantifier-for-subformulae rule (decidable Bool version). Used for if-then-else branching in StringEncoding and premiseOfHighestQuantifier. -/
def isQuantifierRuleBool {L : Language} :
    G2nnfRuleCore L → Bool
  | .allSubLeft _ _ _ _ _ _ _ _ => true
  | .allSubRight _ _ _ _ _ _ _ _ => true
  | .exSubLeft _ _ _ _ _ _ _ _ => true
  | .exSubRight _ _ _ _ _ _ _ _ => true
  | _ => false







-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Example.Proofs
/-- Rule renaming preserves the Boolean quantifier classifier exactly. -/
theorem isQuantifierRuleBool_varMap {L : Language}
    (ρ : Nat → Nat) (rule : G2nnfRuleCore L) :
    (rule.varMap ρ).isQuantifierRuleBool =
      rule.isQuantifierRuleBool := by
  cases rule <;> rfl



end LCS.Herbrand.NNFHauptsatz.G2nnfRuleCore
end

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Soundness
open LCS.Herbrand.SharpenedHauptsatz
open LCS.Herbrand.SharpenedHauptsatz.Permutability
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.Herbrand.PrenexForm
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
open LCS.CutElim.LK
namespace LCS.Herbrand.NNFHauptsatz.G2nnfRule

/-- Extract the cut formula of the equality-free rule, or none for a non-cut rule. -/
@[blueprint "chap7__lemma_7_4_2"]
def cutFormula {L : Language} {hL : L.withoutEquality}
    (rule : G2nnfRule L hL) : Option (FormulaN L) :=
  rule.val.cutFormula

/-- Recognize the four quantifier rules of the equality-free calculus. -/
@[blueprint "chap7__lemma_7_4_2"]
def isQuantifierRule {L : Language} {hL : L.withoutEquality}
    (rule : G2nnfRule L hL) : Prop :=
  rule.val.isQuantifierRule

/-- Recognize the six propositional rules of the equality-free calculus. -/
@[blueprint "chap7__lemma_7_4_2"]
def isPropositionalRule {L : Language} {hL : L.withoutEquality}
    (rule : G2nnfRule L hL) : Prop :=
  rule.val.isPropositionalRule

/-- Recognize left or right weakening in the equality-free calculus. -/
@[blueprint "chap7__lemma_7_4_2"]
def isWeakening {L : Language} {hL : L.withoutEquality}
    (rule : G2nnfRule L hL) : Prop :=
  rule.val.isWeakening

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Boolean classifier for the four equality-free quantifier rules. -/
def isQuantifierRuleBool {L : Language} {hL : L.withoutEquality}
    (rule : G2nnfRule L hL) : Bool :=
  rule.val.isQuantifierRuleBool

end LCS.Herbrand.NNFHauptsatz.G2nnfRule
end

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Soundness
open LCS.Herbrand.SharpenedHauptsatz
open LCS.Herbrand.SharpenedHauptsatz.Permutability
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.Herbrand.PrenexForm
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
open LCS.CutElim.LK
namespace LCS.Herbrand.NNFHauptsatz

-- ATTACH-BLOCKER: private declaration
@[simp] private theorem setMemEmpty_iff (v : Nat) :
    Membership.mem (∅ : Set Nat) v ↔ False := by
  rfl

-- ATTACH-BLOCKER: private declaration
@[simp] private theorem setMemUnion_iff
    (v : Nat) (S T : Set Nat) :
    Membership.mem (S ∪ T) v ↔
      Membership.mem S v ∨ Membership.mem T v := by
  rfl

-- ATTACH-BLOCKER: private declaration
@[simp] private theorem setMemSingleton_iff (v x : Nat) :
    Membership.mem (Set.singleton x) v ↔ v = x := by
  rfl

-- ATTACH-BLOCKER: private declaration
private theorem mem_foldl_append_termVarIndices {L : Language}
    (v : Nat) {β : Type} (f : β → Term L) :
    ∀ (indices : List β) (acc : List Nat),
      v ∈ indices.foldl
          (fun vars i => vars ++ termVarIndicesList (f i)) acc ↔
        v ∈ acc ∨
          ∃ i ∈ indices, v ∈ termVarIndicesList (f i) := by
  intro indices
  induction indices with
  | nil =>
      intro acc
      simp
  | cons i indices ih =>
      intro acc
      simp only [List.foldl]
      rw [ih]
      simp only [List.mem_append, List.mem_cons]
      constructor
      · rintro ((hv | hv) | ⟨j, hj, hv⟩)
        · exact Or.inl hv
        · exact Or.inr ⟨i, Or.inl rfl, hv⟩
        · exact Or.inr ⟨j, Or.inr hj, hv⟩
      · rintro (hv | ⟨j, rfl | hj, hv⟩)
        · exact Or.inl (Or.inl hv)
        · exact Or.inl (Or.inr hv)
        · exact Or.inr ⟨j, hj, hv⟩

-- ATTACH-BLOCKER: private name in relocated declaration
/-- Structural term support contains exactly the variables of the term. -/
theorem mem_termVariableSupport_iff_termVariables {L : Language}
    (t : Term L) (v : Nat) :
    v ∈ termVariableSupport t ↔
      Membership.mem (termVariables t) v := by
  rw [termVariableSupport, LCS.Finset.mem_ofList]
  induction t with
  | var x =>
      simp only [termVarIndicesList, termVariables, List.mem_singleton,
        setMemSingleton_iff]
  | const c =>
      simp only [termVarIndicesList, termVariables, List.not_mem_nil,
        setMemEmpty_iff]
  | func f ts ih =>
      simp only [termVarIndicesList, termVariables]
      rw [mem_foldl_append_termVarIndices]
      simp only [List.not_mem_nil, false_or]
      constructor
      · rintro ⟨i, hi, hv⟩
        exact ⟨i, (ih i).mp hv⟩
      · rintro ⟨i, hv⟩
        exact ⟨i, List.mem_ofFn.mpr ⟨i, rfl⟩, (ih i).mpr hv⟩

-- ATTACH-BLOCKER: private declaration
private theorem mem_formulaVariableIndices_iff_formulaAllVariables
    {L : Language} (A : FormulaN L) (v : Nat) :
    v ∈ formulaVariableIndices A ↔
      Membership.mem (formulaAllVariables A) v := by
  induction A with
  | predN P ts =>
      simp only [formulaVariableIndices, formulaAllVariables]
      rw [mem_foldl_append_termVarIndices]
      simp only [List.not_mem_nil, false_or]
      constructor
      · rintro ⟨i, hi, hv⟩
        exact ⟨i,
          (mem_termVariableSupport_iff_termVariables (ts i) v).mp
            (by
              rw [termVariableSupport, LCS.Finset.mem_ofList]
              exact hv)⟩
      · rintro ⟨i, hv⟩
        refine ⟨i, List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩
        have hv' :
            v ∈ termVariableSupport (ts i) :=
          (mem_termVariableSupport_iff_termVariables (ts i) v).mpr hv
        rw [termVariableSupport, LCS.Finset.mem_ofList] at hv'
        exact hv'
  | eq_ hL t₁ t₂ =>
      simpa only [formulaVariableIndices, formulaAllVariables,
        List.mem_append, termVariableSupport, LCS.Finset.mem_ofList,
        setMemUnion_iff] using
        or_congr
          (mem_termVariableSupport_iff_termVariables t₁ v)
          (mem_termVariableSupport_iff_termVariables t₂ v)
  | neg A ih =>
      simpa only [formulaVariableIndices, formulaAllVariables] using ih
  | conj A B ihA ihB =>
      simpa only [formulaVariableIndices, formulaAllVariables,
        List.mem_append, ihA, ihB, setMemUnion_iff]
  | disj A B ihA ihB =>
      simpa only [formulaVariableIndices, formulaAllVariables,
        List.mem_append, ihA, ihB, setMemUnion_iff]
  | impl A B ihA ihB =>
      simpa only [formulaVariableIndices, formulaAllVariables,
        List.mem_append, ihA, ihB, setMemUnion_iff]
  | all x A ih =>
      simpa only [formulaVariableIndices, formulaAllVariables,
        List.mem_cons, ih, setMemSingleton_iff, setMemUnion_iff]
  | ex x A ih =>
      simpa only [formulaVariableIndices, formulaAllVariables,
        List.mem_cons, ih, setMemSingleton_iff, setMemUnion_iff]

-- ATTACH-BLOCKER: private name in relocated declaration
/-- Structural formula support contains exactly every free or bound variable
of the formula. -/
theorem mem_formulaVariableSupport_iff_formulaAllVariables
    {L : Language} (A : FormulaN L) (v : Nat) :
    v ∈ formulaVariableSupport A ↔
      Membership.mem (formulaAllVariables A) v := by
  rw [formulaVariableSupport, LCS.Finset.mem_ofList]
  exact mem_formulaVariableIndices_iff_formulaAllVariables A v

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Finite term support is mapped exactly by uniform variable renaming. -/
theorem termVariableSupport_termVarMap {L : Language}
    (ρ : Nat → Nat) (t : Term L) :
    termVariableSupport (termVarMap ρ t) =
      LCS.Finset.image ρ (termVariableSupport t) := by
  apply LCS.Finset.ext
  intro z
  rw [mem_termVariableSupport_iff_termVariables,
    termVariables_eq_termFV, termFV_termVarMap_iff,
    LCS.Finset.mem_image]
  constructor
  · rintro ⟨x, hx, hρx⟩
    exact ⟨x,
      (mem_termVariableSupport_iff_termVariables t x).mpr
        (by
          rw [termVariables_eq_termFV]
          exact hx),
      hρx⟩
  · rintro ⟨x, hx, hρx⟩
    exact ⟨x,
      (by
        rw [← termVariables_eq_termFV]
        exact
          (mem_termVariableSupport_iff_termVariables t x).mp hx),
      hρx⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Finite formula support is mapped exactly by uniform variable renaming. -/
theorem formulaVariableSupport_formulaVarMapN {L : Language}
    (ρ : Nat → Nat) (A : FormulaN L) :
    formulaVariableSupport (formulaVarMapN ρ A) =
      LCS.Finset.image ρ (formulaVariableSupport A) := by
  apply LCS.Finset.ext
  intro z
  rw [mem_formulaVariableSupport_iff_formulaAllVariables,
    formulaAllVariables_formulaVarMapN_iff,
    LCS.Finset.mem_image]
  constructor
  · rintro ⟨x, hx, hρx⟩
    exact ⟨x,
      (mem_formulaVariableSupport_iff_formulaAllVariables A x).mpr hx,
      hρx⟩
  · rintro ⟨x, hx, hρx⟩
    exact ⟨x,
      (mem_formulaVariableSupport_iff_formulaAllVariables A x).mp hx,
      hρx⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Finite support of a formula context is mapped exactly. -/
theorem formulaFinsetVariableSupport_formulaFinsetVarMapN
    {L : Language} (ρ : Nat → Nat)
    (S : LCS.Finset (FormulaN L)) :
    formulaFinsetVariableSupport (formulaFinsetVarMapN ρ S) =
      LCS.Finset.image ρ (formulaFinsetVariableSupport S) := by
  apply LCS.Finset.ext
  intro z
  rw [mem_formulaFinsetVariableSupport_iff, LCS.Finset.mem_image]
  constructor
  · rintro ⟨B, hB, hz⟩
    rcases (mem_formulaFinsetVarMapN_iff ρ S B).mp hB with
      ⟨A, hA, rfl⟩
    rw [formulaVariableSupport_formulaVarMapN,
      LCS.Finset.mem_image] at hz
    rcases hz with ⟨x, hx, hρx⟩
    exact ⟨x,
      (mem_formulaFinsetVariableSupport_iff S x).mpr
        ⟨A, hA, hx⟩,
      hρx⟩
  · rintro ⟨x, hx, hρx⟩
    rcases (mem_formulaFinsetVariableSupport_iff S x).mp hx with
      ⟨A, hA, hxA⟩
    refine ⟨formulaVarMapN ρ A,
      (mem_formulaFinsetVarMapN_iff ρ S
        (formulaVarMapN ρ A)).mpr ⟨A, hA, rfl⟩, ?_⟩
    rw [formulaVariableSupport_formulaVarMapN,
      LCS.Finset.mem_image]
    exact ⟨x, hxA, hρx⟩

-- ATTACH-BLOCKER: private declaration
private theorem finsetImage_union {α β : Type}
    [DecidableEq α] [DecidableEq β]
    (f : α → β) (S T : LCS.Finset α) :
    LCS.Finset.image f (LCS.Finset.union S T) =
      LCS.Finset.union (LCS.Finset.image f S)
        (LCS.Finset.image f T) := by
  apply LCS.Finset.ext
  intro b
  rw [LCS.Finset.mem_image, LCS.Finset.mem_union]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases LCS.Finset.mem_union.mp ha with ha | ha
    · exact Or.inl (LCS.Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    · exact Or.inr (LCS.Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  · rintro (hb | hb)
    · rcases LCS.Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
      exact ⟨a, LCS.Finset.mem_union.mpr (Or.inl ha), rfl⟩
    · rcases LCS.Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
      exact ⟨a, LCS.Finset.mem_union.mpr (Or.inr ha), rfl⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Complete finite support of a finite sequent. -/
noncomputable def g2nnfSequentVariableSupport {L : Language}
    (S : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) :
    LCS.Finset Nat :=
  LCS.Finset.union (formulaFinsetVariableSupport S.1)
    (formulaFinsetVariableSupport S.2)

-- ATTACH-BLOCKER: private name in relocated declaration
/-- Sequent support is mapped exactly. -/
theorem g2nnfSequentVariableSupport_varMap {L : Language}
    (ρ : Nat → Nat)
    (S : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) :
    g2nnfSequentVariableSupport (g2nnfSequentVarMap ρ S) =
      LCS.Finset.image ρ (g2nnfSequentVariableSupport S) := by
  simp only [g2nnfSequentVariableSupport, g2nnfSequentVarMap,
    formulaFinsetVariableSupport_formulaFinsetVarMapN]
  exact (finsetImage_union ρ _ _).symm

end LCS.Herbrand.NNFHauptsatz
end

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Soundness
open LCS.Herbrand.SharpenedHauptsatz
open LCS.Herbrand.SharpenedHauptsatz.Permutability
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.Herbrand.PrenexForm
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
open LCS.CutElim.LK
namespace LCS.Herbrand.NNFHauptsatz
namespace MaxQuantifierOccurrence

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Finite support of the proof-relevant occurrence annotation itself.  This
recursion records the selected quantifier principal and every sibling formula
along its exact left/right address. -/
noncomputable def variableSupport {L : Language} :
    {A : FormulaN L} → MaxQuantifierOccurrence A → LCS.Finset Nat
  | _, .all x B =>
      LCS.Finset.insert x (formulaVariableSupport B)
  | _, .ex x B =>
      LCS.Finset.insert x (formulaVariableSupport B)
  | _, .conjLeft occurrence B =>
      LCS.Finset.union occurrence.variableSupport
        (formulaVariableSupport B)
  | _, .conjRight A occurrence =>
      LCS.Finset.union (formulaVariableSupport A)
        occurrence.variableSupport
  | _, .disjLeft occurrence B =>
      LCS.Finset.union occurrence.variableSupport
        (formulaVariableSupport B)
  | _, .disjRight A occurrence =>
      LCS.Finset.union (formulaVariableSupport A)
        occurrence.variableSupport

-- ATTACH-BLOCKER: private name in relocated declaration
/-- Exact occurrence-annotation support is mapped pointwise. -/
theorem variableSupport_varMap {L : Language}
    (ρ : Nat → Nat) {A : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A) :
    (occurrence.varMap ρ).variableSupport =
      LCS.Finset.image ρ occurrence.variableSupport := by
  induction occurrence with
  | all x B =>
      simp only [varMap, variableSupport,
        formulaVariableSupport_formulaVarMapN]
      exact (LCS.Finset.image_insert ρ x
        (formulaVariableSupport B)).symm
  | ex x B =>
      simp only [varMap, variableSupport,
        formulaVariableSupport_formulaVarMapN]
      exact (LCS.Finset.image_insert ρ x
        (formulaVariableSupport B)).symm
  | conjLeft occurrence B ih =>
      simp only [varMap, variableSupport, ih,
        formulaVariableSupport_formulaVarMapN]
      exact (finsetImage_union ρ _ _).symm
  | conjRight A occurrence ih =>
      simp only [varMap, variableSupport, ih,
        formulaVariableSupport_formulaVarMapN]
      exact (finsetImage_union ρ _ _).symm
  | disjLeft occurrence B ih =>
      simp only [varMap, variableSupport, ih,
        formulaVariableSupport_formulaVarMapN]
      exact (finsetImage_union ρ _ _).symm
  | disjRight A occurrence ih =>
      simp only [varMap, variableSupport, ih,
        formulaVariableSupport_formulaVarMapN]
      exact (finsetImage_union ρ _ _).symm

end MaxQuantifierOccurrence
end LCS.Herbrand.NNFHauptsatz
end

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Soundness
open LCS.Herbrand.SharpenedHauptsatz
open LCS.Herbrand.SharpenedHauptsatz.Permutability
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.Herbrand.PrenexForm
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
open LCS.CutElim.LK
namespace LCS.Herbrand.NNFHauptsatz
namespace G2nnfRuleCore

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Finite support of formula, term, binder and selected-occurrence annotations.
Stored side contexts are accounted for separately by `contextSupport`. -/
noncomputable def annotationSupport {L : Language} :
    G2nnfRuleCore L → LCS.Finset Nat
  | .axiomPosId A _ _ _ | .axiomNegId A _ _ _
  | .axiomCompRight A _ _ _ | .axiomCompLeft A _ _ _
  | .weakLeft A _ _ | .weakRight A _ _ | .cut A _ _ _ _ =>
      formulaVariableSupport A
  | .conjLeft1 A B _ _
  | .conjLeft2 A B _ _
  | .conjRight A B _ _
  | .disjLeft A B _ _
  | .disjRight1 A B _ _
  | .disjRight2 A B _ _ =>
      LCS.Finset.union (formulaVariableSupport A)
        (formulaVariableSupport B)
  | .allSubLeft A occurrence x B t _ _ _ =>
      LCS.Finset.insert x
        (LCS.Finset.union (formulaVariableSupport A)
          (LCS.Finset.union occurrence.variableSupport
            (LCS.Finset.union (formulaVariableSupport B)
              (termVariableSupport t))))
  | .allSubRight A occurrence x B y _ _ _
  | .exSubLeft A occurrence x B y _ _ _ =>
      LCS.Finset.insert x
        (LCS.Finset.insert y
          (LCS.Finset.union (formulaVariableSupport A)
            (LCS.Finset.union occurrence.variableSupport
              (formulaVariableSupport B))))
  | .exSubRight A occurrence x B t _ _ _ =>
      LCS.Finset.insert x
        (LCS.Finset.union (formulaVariableSupport A)
          (LCS.Finset.union occurrence.variableSupport
            (LCS.Finset.union (formulaVariableSupport B)
              (termVariableSupport t))))

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Exact support of all stored side contexts. -/
noncomputable def contextSupport {L : Language} : G2nnfRuleCore L → LCS.Finset Nat
  | .cut _ Lambda Theta Gamma Delta =>
      LCS.Finset.union (g2nnfSequentVariableSupport (Gamma, Delta))
        (g2nnfSequentVariableSupport (Lambda, Theta))
  | .axiomPosId _ _ Gamma Delta | .axiomNegId _ _ Gamma Delta
  | .axiomCompRight _ _ Gamma Delta | .axiomCompLeft _ _ Gamma Delta
  | .weakLeft _ Gamma Delta | .weakRight _ Gamma Delta
  | .conjLeft1 _ _ Gamma Delta | .conjLeft2 _ _ Gamma Delta
  | .conjRight _ _ Gamma Delta | .disjLeft _ _ Gamma Delta
  | .disjRight1 _ _ Gamma Delta | .disjRight2 _ _ Gamma Delta
  | .allSubLeft _ _ _ _ _ _ Gamma Delta
  | .allSubRight _ _ _ _ _ _ Gamma Delta
  | .exSubLeft _ _ _ _ _ _ Gamma Delta
  | .exSubRight _ _ _ _ _ _ Gamma Delta =>
      g2nnfSequentVariableSupport (Gamma, Delta)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Complete rule support includes its annotations and every stored context. -/
noncomputable def variableSupport {L : Language} (rule : G2nnfRuleCore L) :
    LCS.Finset Nat := LCS.Finset.union rule.annotationSupport rule.contextSupport

-- ATTACH-BLOCKER: private name in relocated declaration
/-- Full rule-annotation support is mapped exactly. -/
theorem variableSupport_varMap {L : Language}
    (ρ : Nat → Nat) (rule : G2nnfRuleCore L) :
    (rule.varMap ρ).variableSupport =
      LCS.Finset.image ρ rule.variableSupport := by
  cases rule <;>
    simp only [varMap, variableSupport, annotationSupport, contextSupport,
      g2nnfSequentVariableSupport,
      formulaVariableSupport_formulaVarMapN,
      formulaFinsetVariableSupport_formulaFinsetVarMapN,
      termVariableSupport_termVarMap,
      MaxQuantifierOccurrence.variableSupport_varMap,
      LCS.Finset.image_insert, finsetImage_union]

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.VariableSupport.Proofs
/-- A cut formula remains visible in support although it is hidden from the
cut conclusion. -/
theorem variableSupport_cut_formula {L : Language}
    (A : FormulaN L) (Lambda Theta Gamma Delta : LCS.Finset (FormulaN L)) (v : Nat)
    (hv : v ∈ formulaVariableSupport A) :
    v ∈ (G2nnfRuleCore.cut A Lambda Theta Gamma Delta).variableSupport :=
  LCS.Finset.mem_union.mpr (Or.inl hv)













end G2nnfRuleCore
end LCS.Herbrand.NNFHauptsatz
end

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.NNFHauptsatz.Soundness
open LCS.Herbrand.SharpenedHauptsatz
open LCS.Herbrand.SharpenedHauptsatz.Permutability
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.Herbrand.PrenexForm
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
open LCS.CutElim.LK
namespace LCS.Herbrand.NNFHauptsatz.G2nnfProofTree

/-- Lemma 7.4.2 (required def): Predicate asserting that an (indexed) G2nnf proof tree contains no applications of the cut rule. Defined recursively: axiom leaves are vacuously cut-free, and internal nodes require that the rule is not a cut and all subtrees are cut-free. Since `G2nnfProofTree` is indexed by its conclusion sequent in `LCS.Finset (FormulaN L)`, the predicate is defined by structural recursion on the proof tree. -/
@[blueprint "chap7__lemma_7_4_2"]
def isCutFree {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)] :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfProofTree hL Γ Δ → Prop
  | _, _, .leaf _ _ h _ _ => h.elim
  | _, _, .extraAxiom _ _ h _ _ => h.elim
  | _, _, .axiom_ _ _ _ _ => True
  | _, _, .onePremise rule _ _ _ sub =>
    (match rule with
     | .cut _ _ _ _ _ => False
     | _ => True) ∧
    isCutFree (hL := hL) sub
  | _, _, .twoPremise rule _ _ _ sub1 sub2 =>
    (match rule with
     | .cut _ _ _ _ _ => False
     | _ => True) ∧
    isCutFree (hL := hL) sub1 ∧ isCutFree (hL := hL) sub2

/-! ## Complete proof support and canonical root-fixed alpha copies -/

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Complete support contributed by one proof-tree node: its actual
conclusion, every stored side context, and every hidden rule annotation. -/
noncomputable def nodeVariableSupport {L : Language}
    [DecidableEq (FormulaN L)] (rule : G2nnfRuleCore L) : LCS.Finset Nat :=
  LCS.Finset.union (g2nnfSequentVariableSupport rule.conclusion) rule.variableSupport

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Full finite support of a G2nnf proof tree.  This includes every actual
node sequent and all rule-only annotations throughout the tree. -/
noncomputable def variableSupport {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] :
    {Gamma Delta : LCS.Finset (FormulaN L)} →
    G2nnfProofTree hL Gamma Delta → LCS.Finset Nat
  | _, _, .leaf _ _ h _ _ => h.elim
  | _, _, .extraAxiom _ _ h _ _ => h.elim
  | _, _, .axiom_ rule hAdmit _ _ =>
      nodeVariableSupport rule
  | _, _, .onePremise rule hAdmit _ _ sub =>
      LCS.Finset.union (nodeVariableSupport rule)
        (variableSupport (hL := hL) sub)
  | _, _, .twoPremise rule hAdmit _ _ sub1 sub2 =>
      LCS.Finset.union (nodeVariableSupport rule)
        (LCS.Finset.union (variableSupport (hL := hL) sub1) (variableSupport (hL := hL) sub2))

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Exact finite support of the root sequent. -/
noncomputable def rootVariableSupport {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (_ : G2nnfProofTree hL Gamma Delta) : LCS.Finset Nat :=
  g2nnfSequentVariableSupport (Gamma, Delta)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Root support is included in complete proof support. -/
theorem rootVariableSupport_subset_variableSupport
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Gamma Delta) :
    T.rootVariableSupport ⊆ T.variableSupport := by
  intro v hv
  cases T with
  | leaf _ _ h _ _ => exact h.elim
  | extraAxiom _ _ h _ _ => exact h.elim
  | axiom_ rule hAdmit hAxiom hSC =>
      exact LCS.Finset.mem_union.mpr (Or.inl hv)
  | onePremise rule hAdmit hPrem hSC sub =>
      exact LCS.Finset.mem_union.mpr
        (Or.inl (LCS.Finset.mem_union.mpr (Or.inl hv)))
  | twoPremise rule hAdmit hPrem hSC sub1 sub2 =>
      exact LCS.Finset.mem_union.mpr
        (Or.inl (LCS.Finset.mem_union.mpr (Or.inl hv)))

-- ATTACH-BLOCKER: private name in relocated declaration
/-- Node support commutes exactly with injective rule transport. -/
theorem nodeVariableSupport_varMap
    {L : Language} [DecidableEq (FormulaN L)]
    (ρ : Nat → Nat) (rule : G2nnfRuleCore L) :
    nodeVariableSupport (rule.varMap ρ) =
      LCS.Finset.image ρ (nodeVariableSupport rule) := by
  simp only [nodeVariableSupport, G2nnfRuleCore.conclusion_varMap,
    g2nnfSequentVariableSupport, g2nnfSequentVarMap,
    formulaFinsetVariableSupport_formulaFinsetVarMapN,
    G2nnfRuleCore.variableSupport_varMap, finsetImage_union]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Index casts do not alter proof data support. -/
theorem variableSupport_castTree
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Gamma Delta Gamma' Delta' : LCS.Finset (FormulaN L)}
    (hGamma : Gamma = Gamma') (hDelta : Delta = Delta')
    (T : G2nnfProofTree hL Gamma Delta) :
    (T.castTree hGamma hDelta).variableSupport = T.variableSupport := by
  subst Gamma'
  subst Delta'
  rfl

-- ATTACH-BLOCKER: private name in relocated declaration
/-- Complete proof support is the exact image of source support under
uniform injective renaming. -/
theorem variableSupport_varMap
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Gamma Delta) :
    (T.varMap ρ hρ).variableSupport =
      LCS.Finset.image ρ T.variableSupport := by
  induction T with
  | leaf _ _ h _ _ => exact h.elim
  | extraAxiom _ _ h _ _ => exact h.elim
  | axiom_ rule hAdmit hAxiom hSC =>
      simp only [G2nnfProofTree.varMap]
      refine (variableSupport_castTree _ _ _).trans ?_
      simp only [variableSupport,
        variableSupport_castTree, nodeVariableSupport_varMap]
  | onePremise rule hAdmit hPrem hSC sub ih =>
      simp only [G2nnfProofTree.varMap]
      refine (variableSupport_castTree _ _ _).trans ?_
      simp only [variableSupport,
        variableSupport_castTree, nodeVariableSupport_varMap, ih,
        finsetImage_union]
  | twoPremise rule hAdmit hPrem hSC sub1 sub2 ih1 ih2 =>
      simp only [G2nnfProofTree.varMap]
      refine (variableSupport_castTree _ _ _).trans ?_
      simp only [variableSupport,
        variableSupport_castTree, nodeVariableSupport_varMap, ih1, ih2,
        finsetImage_union]

-- ATTACH-BLOCKER: private declaration
private theorem foldlMax_init_le (xs : List Nat) (init : Nat) :
    init ≤ xs.foldl Nat.max init := by
  induction xs generalizing init with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
      exact Nat.le_trans (Nat.le_max_left init x) (ih _)

-- ATTACH-BLOCKER: private declaration
private theorem foldlMax_mem_le (xs : List Nat) (init v : Nat)
    (hv : v ∈ xs) : v ≤ xs.foldl Nat.max init := by
  induction xs generalizing init with
  | nil => simp at hv
  | cons x xs ih =>
      rcases List.mem_cons.mp hv with hvx | hv
      · subst v
        exact Nat.le_trans (Nat.le_max_right init x)
          (foldlMax_init_le xs (Nat.max init x))
      · exact ih (Nat.max init x) hv

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- A deterministic bound strictly above complete source support and every
requested avoidance value. -/
noncomputable def freshAlphaBound {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Gamma Delta)
    (avoid : LCS.Finset Nat) : Nat :=
  (LCS.Finset.union T.variableSupport avoid).toList.foldl Nat.max 0 + 1

-- ATTACH-BLOCKER: private name in relocated declaration
/-- Every source-support value lies strictly below the alpha bound. -/
theorem variableSupport_lt_freshAlphaBound
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Gamma Delta)
    (avoid : LCS.Finset Nat) (v : Nat)
    (hv : v ∈ T.variableSupport) :
    v < T.freshAlphaBound avoid := by
  have hList :
      v ∈ (LCS.Finset.union T.variableSupport avoid).toList :=
    (LCS.Finset.mem_toList
      (LCS.Finset.union T.variableSupport avoid) v).mpr
      (LCS.Finset.mem_union.mpr (Or.inl hv))
  have hLe := foldlMax_mem_le
    (LCS.Finset.union T.variableSupport avoid).toList 0 v hList
  simp only [freshAlphaBound]
  omega

-- ATTACH-BLOCKER: private name in relocated declaration
/-- Every avoidance value lies strictly below the alpha bound, including
arbitrarily large requested values. -/
theorem avoid_lt_freshAlphaBound
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Gamma Delta)
    (avoid : LCS.Finset Nat) (v : Nat)
    (hv : v ∈ avoid) :
    v < T.freshAlphaBound avoid := by
  have hList :
      v ∈ (LCS.Finset.union T.variableSupport avoid).toList :=
    (LCS.Finset.mem_toList
      (LCS.Finset.union T.variableSupport avoid) v).mpr
      (LCS.Finset.mem_union.mpr (Or.inr hv))
  have hLe := foldlMax_mem_le
    (LCS.Finset.union T.variableSupport avoid).toList 0 v hList
  simp only [freshAlphaBound]
  omega

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Canonical root-fixed alpha renaming.  Root variables are unchanged;
every other variable is shifted beyond complete source and avoidance
support. -/
noncomputable def freshAlphaRenaming
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Gamma Delta)
    (avoid : LCS.Finset Nat) (x : Nat) : Nat :=
  if x ∈ T.rootVariableSupport then x
  else x + T.freshAlphaBound avoid

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The canonical alpha renaming fixes every root variable. -/
theorem freshAlphaRenaming_fixed_root
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Gamma Delta)
    (avoid : LCS.Finset Nat) (x : Nat)
    (hx : x ∈ T.rootVariableSupport) :
    T.freshAlphaRenaming avoid x = x := by
  simp [freshAlphaRenaming, hx]

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Off-root variables are shifted at least to the fresh bound. -/
theorem freshAlphaBound_le_freshAlphaRenaming_of_not_root
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Gamma Delta)
    (avoid : LCS.Finset Nat) (x : Nat)
    (hx : x ∉ T.rootVariableSupport) :
    T.freshAlphaBound avoid ≤ T.freshAlphaRenaming avoid x := by
  simp only [freshAlphaRenaming, if_neg hx]
  omega

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Paths, LCS.Herbrand.NNFHauptsatz.Theorem.Purity, LCS.Herbrand.NNFHauptsatz.Theorem.Purity.Proofs
/-- The canonical root-fixed alpha renaming is injective on all naturals. -/
theorem freshAlphaRenaming_injective
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Gamma Delta)
    (avoid : LCS.Finset Nat) :
    Function.Injective (T.freshAlphaRenaming avoid) := by
  intro x y hxy
  by_cases hx : x ∈ T.rootVariableSupport
  · by_cases hy : y ∈ T.rootVariableSupport
    · simpa [freshAlphaRenaming, hx, hy] using hxy
    · have hxSupport : x ∈ T.variableSupport :=
        T.rootVariableSupport_subset_variableSupport x hx
      have hxLt :=
        T.variableSupport_lt_freshAlphaBound avoid x hxSupport
      have hyLe :=
        T.freshAlphaBound_le_freshAlphaRenaming_of_not_root
          avoid y hy
      rw [T.freshAlphaRenaming_fixed_root avoid x hx] at hxy
      omega
  · by_cases hy : y ∈ T.rootVariableSupport
    · have hySupport : y ∈ T.variableSupport :=
        T.rootVariableSupport_subset_variableSupport y hy
      have hyLt :=
        T.variableSupport_lt_freshAlphaBound avoid y hySupport
      have hxLe :=
        T.freshAlphaBound_le_freshAlphaRenaming_of_not_root
          avoid x hx
      rw [T.freshAlphaRenaming_fixed_root avoid y hy] at hxy
      omega
    · simp only [freshAlphaRenaming, if_neg hx, if_neg hy] at hxy
      omega

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Paths
/-- An off-root source variable maps outside complete source support. -/
theorem freshAlphaRenaming_off_root_not_mem_variableSupport
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Gamma Delta)
    (avoid : LCS.Finset Nat) (x : Nat)
    (hx : x ∉ T.rootVariableSupport) :
    T.freshAlphaRenaming avoid x ∉ T.variableSupport := by
  intro hMem
  have hLt := T.variableSupport_lt_freshAlphaBound avoid
    (T.freshAlphaRenaming avoid x) hMem
  have hLe :=
    T.freshAlphaBound_le_freshAlphaRenaming_of_not_root avoid x hx
  omega

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.Paths
/-- An off-root source variable also maps outside the explicit avoidance
support. -/
theorem freshAlphaRenaming_off_root_not_mem_avoid
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Gamma Delta)
    (avoid : LCS.Finset Nat) (x : Nat)
    (hx : x ∉ T.rootVariableSupport) :
    T.freshAlphaRenaming avoid x ∉ avoid := by
  intro hMem
  have hLt := T.avoid_lt_freshAlphaBound avoid
    (T.freshAlphaRenaming avoid x) hMem
  have hLe :=
    T.freshAlphaBound_le_freshAlphaRenaming_of_not_root avoid x hx
  omega

end LCS.Herbrand.NNFHauptsatz.G2nnfProofTree
end

