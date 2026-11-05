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
import LCS.Herbrand.NNFHauptsatz.Theorem.VariableSupport
import LCS.Herbrand.NNFHauptsatz.Theorem.Paths
import Attach
import LCS.Herbrand.NNFHauptsatz.Theorem.Purity.ProofsStamp

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
namespace LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree
open LCS.Herbrand.NNFHauptsatz.G2nnfRule





-- ===================================================================
-- Lemma 7.4.2 (required def): IsPureVariableProofG2nnf
-- ===================================================================

/-- Lemma 7.4.2 (companion def): The occurrence-aware form of the
pure-variable predicate for G2nnf.  The `outer` proof tree stays fixed while
the recursive `current` tree is accompanied by its exact root-to-node path in
`outer`.  At an eigenvariable-introducing rule, extending that path through
the sole premise identifies the precise exempt premise occurrence. -/
@[blueprint "chap7__lemma_7_4_2"]
def isPureVariableProofG2nnfAux {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    (outer : G2nnfProofTree hL Γroot Δroot) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    (current : G2nnfProofTree hL Γ Δ) →
    RootToNodePath outer current → Prop
  | _, _, .leaf _ _ h _ _, _ => h.elim
  | _, _, .extraAxiom _ _ h _ _, _ => h.elim
  | _, _, .axiom_ _ _ _ _, _ => True
  | _, _, .onePremise rule hAdmit hPrem hSC sub, path =>
    let subPath : RootToNodePath outer sub :=
      path.trans
        (.onePremise rule hAdmit hPrem hSC sub (.root sub))
    let subOccurrence : NodeOccurrence outer _ _ := ⟨sub, subPath⟩
    (match rule with
     | .allSubRight _ _ _ _ y _ _ _ =>
       g2nnfNoFreeBoundOverlap y outer ∧
       g2nnfEigenvariableOccursOnlyInSubtree y subOccurrence
     | .exSubLeft _ _ _ _ y _ _ _ =>
       g2nnfNoFreeBoundOverlap y outer ∧
       g2nnfEigenvariableOccursOnlyInSubtree y subOccurrence
     | _ => True) ∧
    isPureVariableProofG2nnfAux outer sub subPath
  | _, _, .twoPremise rule hAdmit hPrem hSC sub1 sub2, path =>
    let leftPath : RootToNodePath outer sub1 :=
      path.trans
        (.leftPremise rule hAdmit hPrem hSC sub1 sub2 (.root sub1))
    let rightPath : RootToNodePath outer sub2 :=
      path.trans
        (.rightPremise rule hAdmit hPrem hSC sub1 sub2 (.root sub2))
    isPureVariableProofG2nnfAux outer sub1 leftPath ∧
    isPureVariableProofG2nnfAux outer sub2 rightPath

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- A zero-step index bridge at the current node preserves the auxiliary
purity condition while making the cast explicit in the path. -/
theorem isPureVariableProofG2nnfAux_castBridge_iff
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {GammaRoot DeltaRoot Gamma Delta Gamma' Delta' :
      LCS.Finset (FormulaN L)}
    (outer : G2nnfProofTree hL GammaRoot DeltaRoot)
    (current : G2nnfProofTree hL Gamma Delta)
    (hGamma : Gamma = Gamma')
    (hDelta : Delta = Delta')
    (path : RootToNodePath outer
      (current.castTree hGamma hDelta)) :
    isPureVariableProofG2nnfAux outer
        (current.castTree hGamma hDelta) path ↔
      isPureVariableProofG2nnfAux outer current
        (path.trans
          ((RootToNodePath.root current).castRoot hGamma hDelta)) := by
  cases hGamma
  cases hDelta
  change RootToNodePath outer current at path
  simpa only [G2nnfProofTree.castTree, RootToNodePath.castRoot,
    RootToNodePath.trans_root]



/-- Lemma 7.4.2 (required def): Predicate asserting that a G2nnf proof tree is
pure-variable (adapted from Definition 7.3.1 for G2nnf).  The root occurrence
starts the recursion; every descent extends its path while retaining the same
outer tree, so nested eigenvariable rules are checked against exact premise
occurrences in the whole proof tree. -/
@[blueprint "chap7__lemma_7_4_2"]
def IsPureVariableProofG2nnf {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Γ Δ) : Prop :=
  isPureVariableProofG2nnfAux T T (.root T)

/-- Section 7.4.3: Lemma 7.3.1 extends to G2nnf. Retain each rule kind,
selected quantifier address, context, formula, term, and variable annotation. -/
def g2nnfRenamingRuleData {L : Language} : G2nnfRuleCore L →
    Nat × MaxQuantifierOccurrenceAddress × List (LCS.Finset (FormulaN L)) ×
      List (FormulaN L) × List (Term L) × List Nat
  | .axiomPosId A _ Γ Δ => (0, [], [Γ, Δ], [A], [], [])
  | .axiomNegId A _ Γ Δ => (1, [], [Γ, Δ], [A], [], [])
  | .axiomCompRight A _ Γ Δ => (2, [], [Γ, Δ], [A], [], [])
  | .axiomCompLeft A _ Γ Δ => (3, [], [Γ, Δ], [A], [], [])
  | .weakLeft A Γ Δ => (4, [], [Γ, Δ], [A], [], [])
  | .weakRight A Γ Δ => (5, [], [Γ, Δ], [A], [], [])
  | .conjLeft1 A B Γ Δ => (6, [], [Γ, Δ], [A, B], [], [])
  | .conjLeft2 A B Γ Δ => (7, [], [Γ, Δ], [A, B], [], [])
  | .conjRight A B Γ Δ => (8, [], [Γ, Δ], [A, B], [], [])
  | .disjLeft A B Γ Δ => (9, [], [Γ, Δ], [A, B], [], [])
  | .disjRight1 A B Γ Δ => (10, [], [Γ, Δ], [A, B], [], [])
  | .disjRight2 A B Γ Δ => (11, [], [Γ, Δ], [A, B], [], [])
  | .cut A Λ Θ Γ Δ => (12, [], [Γ, Δ, Λ, Θ], [A], [], [])
  | .allSubLeft A o x B t _ Γ Δ => (13, o.address, [Γ, Δ], [A, .all x B], [t], [x])
  | .allSubRight A o x B y _ Γ Δ => (14, o.address, [Γ, Δ], [A, .all x B], [.var y], [y, x])
  | .exSubLeft A o x B y _ Γ Δ => (15, o.address, [Γ, Δ], [A, .ex x B], [.var y], [y, x])
  | .exSubRight A o x B t _ Γ Δ => (16, o.address, [Γ, Δ], [A, .ex x B], [t], [x])

/-- Section 7.4.3: Lemma 7.3.1 extends to G2nnf. Read the rule at an
ordered tree address; absent addresses remain absent under renaming. -/
def g2nnfRenamingRuleAt {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] : {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfProofTree hL Γ Δ → List Nat → Option (G2nnfRuleCore L)
  | _, _, .leaf _ _ h _ _, _ => h.elim
  | _, _, .extraAxiom _ _ h _ _, _ => h.elim
  | _, _, .axiom_ r _ _ _, [] => some r
  | _, _, .onePremise r _ _ _ _, [] => some r
  | _, _, .twoPremise r _ _ _ _ _, [] => some r
  | _, _, .onePremise _ _ _ _ t, 0 :: p => g2nnfRenamingRuleAt (hL := hL) t p
  | _, _, .twoPremise _ _ _ _ t _, 0 :: p => g2nnfRenamingRuleAt (hL := hL) t p
  | _, _, .twoPremise _ _ _ _ _ t, 1 :: p => g2nnfRenamingRuleAt (hL := hL) t p
  | _, _, _, _ => none

/-- Section 7.4.3: Lemma 7.3.1 extends to G2nnf. Renaming preserves the
end sequent, ordered tree, rule kinds, and selected quantifier occurrences.
At each node the LK replacement relation checks all annotations together;
context enumerations respect finite-set equality, not an arbitrary order.
Changed names are fresh for the entire source proof, including hidden terms. -/
@[blueprint "chap7__definition_7_4_3"]
def proofVariableReplacementG2nnf {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] {Γ Δ : LCS.Finset (FormulaN L)}
    (T T' : G2nnfProofTree hL Γ Δ) : Prop :=
  ∀ p, match g2nnfRenamingRuleAt T p, g2nnfRenamingRuleAt T' p with
    | none, none => True
    | some r, some r' =>
      let (k, address, contexts, formulas, terms, variables) := g2nnfRenamingRuleData r
      let (k', address', contexts', formulas', terms', variables') := g2nnfRenamingRuleData r'
      address = address' ∧ ∃ blocks : List (List (FormulaN L)),
        blocks.map LCS.Finset.ofList = contexts' ∧
        replacementNodeRelated (fun y => y ∉ T.variableSupport)
          (k, formulas :: contexts.map LCS.Finset.toList, terms, variables)
          (k', formulas' :: blocks, terms', variables')
    | _, _ => False

/-- Section 7.4.3: Lemma 7.3.1 extends to G2nnf. Every supplied proof
can be converted by renaming variables to a pure-variable proof of the same sequent. -/
@[attach_debt, blueprint "chap7__definition_7_4_3"]
theorem g2nnf_pureVariableConversion {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Γ Δ) :
    ∃ T' : G2nnfProofTree hL Γ Δ,
      IsPureVariableProofG2nnf T' ∧ proofVariableReplacementG2nnf T T'

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The occurrence-aware auxiliary purity predicate is preserved by
injective uniform renaming of its fixed outer tree, current node, and exact
path. -/
theorem isPureVariableProofG2nnfAux_varMap
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    {GammaRoot DeltaRoot Gamma Delta :
      LCS.Finset (FormulaN L)}
    (outer : G2nnfProofTree hL GammaRoot DeltaRoot)
    (current : G2nnfProofTree hL Gamma Delta)
    (path : RootToNodePath outer current)
    (hPure : isPureVariableProofG2nnfAux outer current path) :
    isPureVariableProofG2nnfAux
      (outer.varMap ρ hρ) (current.varMap ρ hρ)
      (path.varMap ρ hρ) := by
  induction current generalizing GammaRoot DeltaRoot outer with
  | leaf _ _ h _ _ => exact h.elim
  | extraAxiom _ _ h _ _ => exact h.elim
  | axiom_ rule hAdmit hAxiom hSC =>
      apply (isPureVariableProofG2nnfAux_castBridge_iff _ _ _ _ _).mpr
      trivial
  | onePremise rule hAdmit hPrem hSC sub ih =>
      let sourceStep : RootToNodePath (hL := hL)
          (.onePremise rule hAdmit hPrem hSC sub) sub :=
        .onePremise rule hAdmit hPrem hSC sub (.root sub)
      let sourceSubPath := path.trans sourceStep
      have hRec := ih outer sourceSubPath hPure.2
      apply (isPureVariableProofG2nnfAux_castBridge_iff _ _ _ _ _).mpr
      constructor
      · cases rule with
        | allSubRight A occurrence x B y hSelected Gamma Delta =>
            constructor
            · exact g2nnfNoFreeBoundOverlap_of_proofTree _ _
            · have hOnly := g2nnfEigenvariableOccursOnlyInSubtree_varMap
                ρ hρ y (⟨sub, sourceSubPath⟩ : NodeOccurrence outer _ _) hPure.1.2
              change g2nnfVariableOccursOnlyAlongPath (ρ y) _
              apply (g2nnfVariableOccursOnlyAlongPath_castedStep_iff
                (ρ y) _ (G2nnfProofTree.varMap (hL := hL) ρ hρ sub) _ _ _ _ _ _).mp
              exact Eq.mp (congrArg (g2nnfVariableOccursOnlyAlongPath (ρ y))
                (RootToNodePath.varMap_trans ρ hρ path sourceStep)) hOnly
        | exSubLeft A occurrence x B y hSelected Gamma Delta =>
            constructor
            · exact g2nnfNoFreeBoundOverlap_of_proofTree _ _
            · have hOnly := g2nnfEigenvariableOccursOnlyInSubtree_varMap
                ρ hρ y (⟨sub, sourceSubPath⟩ : NodeOccurrence outer _ _) hPure.1.2
              change g2nnfVariableOccursOnlyAlongPath (ρ y) _
              apply (g2nnfVariableOccursOnlyAlongPath_castedStep_iff
                (ρ y) _ (G2nnfProofTree.varMap (hL := hL) ρ hρ sub) _ _ _ _ _ _).mp
              exact Eq.mp (congrArg (g2nnfVariableOccursOnlyAlongPath (ρ y))
                (RootToNodePath.varMap_trans ρ hρ path sourceStep)) hOnly
        | _ => trivial
      · apply (isPureVariableProofG2nnfAux_castBridge_iff _ _ _ _ _).mpr
        apply Eq.mpr (congrArg (isPureVariableProofG2nnfAux _ _)
          (RootToNodePath.castBridge_trans_castedStep _ _ _ _ _ _ _ _))
        exact Eq.mp (congrArg (isPureVariableProofG2nnfAux _ _)
          (RootToNodePath.varMap_trans ρ hρ path sourceStep)) hRec
  | twoPremise rule hAdmit hPrem hSC sub1 sub2 ih1 ih2 =>
      let leftStep : RootToNodePath (hL := hL)
          (.twoPremise rule hAdmit hPrem hSC sub1 sub2) sub1 :=
        .leftPremise rule hAdmit hPrem hSC sub1 sub2 (.root sub1)
      let rightStep : RootToNodePath (hL := hL)
          (.twoPremise rule hAdmit hPrem hSC sub1 sub2) sub2 :=
        .rightPremise rule hAdmit hPrem hSC sub1 sub2 (.root sub2)
      have hLeft := ih1 outer (path.trans leftStep) hPure.1
      have hRight := ih2 outer (path.trans rightStep) hPure.2
      apply (isPureVariableProofG2nnfAux_castBridge_iff _ _ _ _ _).mpr
      constructor
      · apply (isPureVariableProofG2nnfAux_castBridge_iff _ _ _ _ _).mpr
        apply Eq.mpr (congrArg (isPureVariableProofG2nnfAux _ _)
          (RootToNodePath.castBridge_trans_castedStep _ _ _ _ _ _ _ _))
        exact Eq.mp (congrArg (isPureVariableProofG2nnfAux _ _)
          (RootToNodePath.varMap_trans ρ hρ path leftStep)) hLeft
      · apply (isPureVariableProofG2nnfAux_castBridge_iff _ _ _ _ _).mpr
        apply Eq.mpr (congrArg (isPureVariableProofG2nnfAux _ _)
          (RootToNodePath.castBridge_trans_castedStep _ _ _ _ _ _ _ _))
        exact Eq.mp (congrArg (isPureVariableProofG2nnfAux _ _)
          (RootToNodePath.varMap_trans ρ hρ path rightStep)) hRight

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Public G2nnf purity is preserved by injective uniform renaming. -/
theorem IsPureVariableProofG2nnf.varMap
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Gamma Delta)
    (hPure : IsPureVariableProofG2nnf T) :
    IsPureVariableProofG2nnf (T.varMap ρ hρ) := by
  exact isPureVariableProofG2nnfAux_varMap
    ρ hρ T T (.root T) hPure

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Index casts preserve the public purity predicate exactly. -/
theorem IsPureVariableProofG2nnf.castTree_iff
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Gamma Delta Gamma' Delta' : LCS.Finset (FormulaN L)}
    (hGamma : Gamma = Gamma') (hDelta : Delta = Delta')
    (T : G2nnfProofTree hL Gamma Delta) :
    IsPureVariableProofG2nnf (T.castTree hGamma hDelta) ↔
      IsPureVariableProofG2nnf T := by
  subst Gamma'
  subst Delta'
  rfl

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The canonical same-root alpha copy preserves occurrence-aware purity. -/
theorem IsPureVariableProofG2nnf.freshAlphaCopy
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Gamma Delta)
    (avoid : LCS.Finset Nat)
    (hPure : IsPureVariableProofG2nnf T) :
    IsPureVariableProofG2nnf (T.freshAlphaCopy avoid) := by
  rw [G2nnfProofTree.freshAlphaCopy,
    IsPureVariableProofG2nnf.castTree_iff]
  exact IsPureVariableProofG2nnf.varMap
    (T.freshAlphaRenaming avoid)
    (T.freshAlphaRenaming_injective avoid) T hPure

/-- Definition 7.4.3: the four bare axiom sequents on an atomic A.
The negated identity and complementary-literal schemes retain their literal
negations; there are no additional antecedent or succedent contexts. -/
@[blueprint "chap7__definition_7_4_3"]
def IsBareAtomicLeafSequent {L : Language} (_hL : L.withoutEquality)
    [DecidableEq (FormulaN L)]
    (seq : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) : Prop :=
  ∃ A : FormulaN L, A.isAtomic ∧
    (seq = (LCS.Finset.insert A LCS.Finset.empty,
            LCS.Finset.insert A LCS.Finset.empty) ∨
     seq = (LCS.Finset.empty,
            LCS.Finset.insert A (LCS.Finset.insert (.neg A) LCS.Finset.empty)) ∨
     seq = (LCS.Finset.insert A (LCS.Finset.insert (.neg A) LCS.Finset.empty),
            LCS.Finset.empty) ∨
     seq = (LCS.Finset.insert (.neg A) LCS.Finset.empty,
            LCS.Finset.insert (.neg A) LCS.Finset.empty))

/-- Definition 7.4.3 (atomic-leaf extension): every terminal sequent is one
of the four bare atomic schemes. Both branches of a binary inference are
checked; open leaves and extra axioms do not satisfy this predicate. -/
@[blueprint "chap7__definition_7_4_3"]
def HasBareAtomicLeaves {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] :
    {Γ Δ : LCS.Finset (FormulaN L)} → G2nnfProofTree hL Γ Δ → Prop
  | _, _, .leaf .. => False
  | _, _, .extraAxiom .. => False
  | _, _, .axiom_ rule _ _ _ => IsBareAtomicLeafSequent hL rule.conclusion
  | _, _, .onePremise _ _ _ _ sub => HasBareAtomicLeaves (hL := hL) sub
  | _, _, .twoPremise _ _ _ _ left right =>
    HasBareAtomicLeaves (hL := hL) left ∧ HasBareAtomicLeaves (hL := hL) right

/-- Section 7.4.3 extends the atomic-leaf lemma to G2nnf. In Definition
7.4.3's corrected calculus, every proof already has bare atomic leaves,
including proofs with cuts and proofs not assumed pure-variable. -/
@[blueprint "chap7__definition_7_4_3"]
theorem g2nnf_hasBareAtomicLeaves {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Γ Δ) : HasBareAtomicLeaves (hL := hL) T 



-- ===================================================================
-- Lemma 7.4.2 (untagged infrastructure): exact permutation occurrences
-- ===================================================================

/-- The side of a sequent on which a quantifier rule's principal formula
occurs.  This is deliberately untagged proof infrastructure for the local
permutation relation. -/
@[blueprint "chap7__lemma_7_4_3", blueprint "chap7__definition_7_4_3", blueprint "chap7__lemma_7_4_2"]
inductive G2nnfSequentSide where
  | left
  | right
deriving DecidableEq

/-- Select the raw context on the side of a quantifier principal formula. -/
@[blueprint "chap7__lemma_7_4_3", blueprint "chap7__lemma_7_4_2"]
def G2nnfSequentSide.context {L : Language}
    (side : G2nnfSequentSide)
    (Gamma Delta : LCS.Finset (FormulaN L)) :
    LCS.Finset (FormulaN L) :=
  match side with
  | .left => Gamma
  | .right => Delta

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The weakening rule which adds a formula on the selected sequent side. -/
def G2nnfSequentSide.weakeningRule {L : Language}
    (side : G2nnfSequentSide) (A : FormulaN L)
    (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L :=
  match side with
  | .left => .weakLeft A Gamma Delta
  | .right => .weakRight A Gamma Delta

/-- Constructor-exact evidence that a rule is one of the four G2nnf
quantifier rules.  Unlike `isQuantifierRule`, this view exposes the principal
formula and its sequent side without recovering them from rule-value
equalities. -/
@[blueprint "chap7__definition_7_4_3"]
inductive G2nnfQuantifierRuleView {L : Language} :
    G2nnfRuleCore L → Type where
  | allSubLeft (A : FormulaN L)
      (occurrence : MaxQuantifierOccurrence A)
      (x : Nat) (B : FormulaN L) (t : Term L)
      (hSelected : occurrence.selected = FormulaN.all x B)
      (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfQuantifierRuleView
        (.allSubLeft A occurrence x B t hSelected Gamma Delta)
  | allSubRight (A : FormulaN L)
      (occurrence : MaxQuantifierOccurrence A)
      (x : Nat) (B : FormulaN L) (y : Nat)
      (hSelected : occurrence.selected = FormulaN.all x B)
      (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfQuantifierRuleView
        (.allSubRight A occurrence x B y hSelected Gamma Delta)
  | exSubLeft (A : FormulaN L)
      (occurrence : MaxQuantifierOccurrence A)
      (x : Nat) (B : FormulaN L) (y : Nat)
      (hSelected : occurrence.selected = FormulaN.ex x B)
      (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfQuantifierRuleView
        (.exSubLeft A occurrence x B y hSelected Gamma Delta)
  | exSubRight (A : FormulaN L)
      (occurrence : MaxQuantifierOccurrence A)
      (x : Nat) (B : FormulaN L) (t : Term L)
      (hSelected : occurrence.selected = FormulaN.ex x B)
      (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfQuantifierRuleView
        (.exSubRight A occurrence x B t hSelected Gamma Delta)

end LCS.Herbrand.NNFHauptsatz.Theorem
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
namespace LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree
open LCS.Herbrand.NNFHauptsatz.G2nnfRule
namespace G2nnfQuantifierRuleView

/-- The exact principal formula carried by a quantifier-rule view. -/
@[blueprint "chap7__definition_7_4_3"]
def principal {L : Language} {rule : G2nnfRuleCore L} :
    G2nnfQuantifierRuleView rule → FormulaN L
  | .allSubLeft A _ _ _ _ _ _ _ => A
  | .allSubRight A _ _ _ _ _ _ _ => A
  | .exSubLeft A _ _ _ _ _ _ _ => A
  | .exSubRight A _ _ _ _ _ _ _ => A

/-- The side on which the viewed quantifier rule acts. -/
@[blueprint "chap7__definition_7_4_3"]
def side {L : Language} {rule : G2nnfRuleCore L} :
    G2nnfQuantifierRuleView rule → G2nnfSequentSide
  | .allSubLeft _ _ _ _ _ _ _ _ => .left
  | .allSubRight _ _ _ _ _ _ _ _ => .right
  | .exSubLeft _ _ _ _ _ _ _ _ => .left
  | .exSubRight _ _ _ _ _ _ _ _ => .right

/-- The exact maximal occurrence carried by the viewed rule. -/
@[blueprint "chap7__lemma_7_4_3"]
def occurrence {L : Language} {rule : G2nnfRuleCore L}
    (view : G2nnfQuantifierRuleView rule) :
    MaxQuantifierOccurrence view.principal :=
  match view with
  | .allSubLeft _ occurrence _ _ _ _ _ _ => occurrence
  | .allSubRight _ occurrence _ _ _ _ _ _ => occurrence
  | .exSubLeft _ occurrence _ _ _ _ _ _ => occurrence
  | .exSubRight _ occurrence _ _ _ _ _ _ => occurrence

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The substitution result inserted at the exact selected occurrence. -/
@[blueprint "chap7__lemma_7_4_2"]
def replacement {L : Language} {rule : G2nnfRuleCore L}
    (view : G2nnfQuantifierRuleView rule) : FormulaN L :=
  match view with
  | .allSubLeft _ _ x B t _ _ _ => formulaSubstN B t x
  | .allSubRight _ _ x B y _ _ _ => formulaSubstN B (.var y) x
  | .exSubLeft _ _ x B y _ _ _ => formulaSubstN B (.var y) x
  | .exSubRight _ _ x B t _ _ _ => formulaSubstN B t x

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The principal formula in the premise of the viewed quantifier rule. -/
@[blueprint "chap7__lemma_7_4_2"]
def premisePrincipal {L : Language}
    {rule : G2nnfRuleCore L}
    (view : G2nnfQuantifierRuleView rule) : FormulaN L :=
  view.occurrence.replace view.replacement

/-- Rebuild the same quantifier schema at a new principal only when the
caller supplies the exact transported occurrence.  The selected formula must
be the same one selected by the source rule. The caller supplies the output
side contexts of the rebuilt instance. -/
@[blueprint "chap7__lemma_7_4_3"]
def reprincipalAt {L : Language} {rule : G2nnfRuleCore L}
    (view : G2nnfQuantifierRuleView rule) {A' : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A')
    (hSameSelected : occurrence.selected = view.occurrence.selected)
    (Gamma Delta : LCS.Finset (FormulaN L)) :
    G2nnfRuleCore L :=
  match view with
  | .allSubLeft _ _ x B t hSelected _ _ =>
      .allSubLeft A' occurrence x B t
        (hSameSelected.trans hSelected) Gamma Delta
  | .allSubRight _ _ x B y hSelected _ _ =>
      .allSubRight A' occurrence x B y
        (hSameSelected.trans hSelected) Gamma Delta
  | .exSubLeft _ _ x B y hSelected _ _ =>
      .exSubLeft A' occurrence x B y
        (hSameSelected.trans hSelected) Gamma Delta
  | .exSubRight _ _ x B t hSelected _ _ =>
      .exSubRight A' occurrence x B t
        (hSameSelected.trans hSelected) Gamma Delta

end G2nnfQuantifierRuleView
end LCS.Herbrand.NNFHauptsatz.Theorem
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
namespace LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree
open LCS.Herbrand.NNFHauptsatz.G2nnfRule

/-- Definition 7.3.2, as extended in §7.4.3: the lower rule may be any
G2nnf rule with a premise, including a quantifier rule or cut. The extension
restricts the intervening structural section to weakenings only. -/
@[blueprint "chap7__lemma_7_4_2"]
inductive G2nnfPermutationLowerRuleView {L : Language} :
    G2nnfRuleCore L → Type where
  | weakLeft (A : FormulaN L) (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfPermutationLowerRuleView (.weakLeft A Gamma Delta)
  | weakRight (A : FormulaN L) (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfPermutationLowerRuleView (.weakRight A Gamma Delta)
  | conjLeft1 (A B : FormulaN L) (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfPermutationLowerRuleView (.conjLeft1 A B Gamma Delta)
  | conjLeft2 (A B : FormulaN L) (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfPermutationLowerRuleView (.conjLeft2 A B Gamma Delta)
  | conjRight (A B : FormulaN L) (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfPermutationLowerRuleView (.conjRight A B Gamma Delta)
  | disjLeft (A B : FormulaN L) (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfPermutationLowerRuleView (.disjLeft A B Gamma Delta)
  | disjRight1 (A B : FormulaN L) (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfPermutationLowerRuleView (.disjRight1 A B Gamma Delta)
  | disjRight2 (A B : FormulaN L) (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfPermutationLowerRuleView (.disjRight2 A B Gamma Delta)

  | cut (A : FormulaN L) (Lambda Theta : LCS.Finset (FormulaN L))
      (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfPermutationLowerRuleView (.cut A Lambda Theta Gamma Delta)
  /-- Forall-subformula left: replace exactly the selected maximal occurrence
      of `forall x B` by `B[t/x]`.  The occurrence and its selected-formula
      equation are constructor data, so duplicate equal formulae remain
      distinct and QF-membership is enforced structurally. -/
  | allSubLeft (A : FormulaN L)
      (occurrence : MaxQuantifierOccurrence A) (x : Nat)
      (B : FormulaN L) (t : Term L)
      (hSelected : occurrence.selected = FormulaN.all x B)
      (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfPermutationLowerRuleView (.allSubLeft A occurrence x B t hSelected Gamma Delta)
  /-- Forall-subformula right: replace exactly the selected maximal occurrence
      of `forall x B` by `B[y/x]`; `y` is fresh for the lower sequent. -/
  | allSubRight (A : FormulaN L)
      (occurrence : MaxQuantifierOccurrence A) (x : Nat)
      (B : FormulaN L) (y : Nat)
      (hSelected : occurrence.selected = FormulaN.all x B)
      (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfPermutationLowerRuleView (.allSubRight A occurrence x B y hSelected Gamma Delta)
  /-- Exists-subformula left: replace exactly the selected maximal occurrence
      of `exists x B` by `B[y/x]`; `y` is fresh for the lower sequent. -/
  | exSubLeft (A : FormulaN L)
      (occurrence : MaxQuantifierOccurrence A) (x : Nat)
      (B : FormulaN L) (y : Nat)
      (hSelected : occurrence.selected = FormulaN.ex x B)
      (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfPermutationLowerRuleView (.exSubLeft A occurrence x B y hSelected Gamma Delta)
  /-- Exists-subformula right: replace exactly the selected maximal occurrence
      of `exists x B` by `B[t/x]`. -/
  | exSubRight (A : FormulaN L)
      (occurrence : MaxQuantifierOccurrence A) (x : Nat)
      (B : FormulaN L) (t : Term L)
      (hSelected : occurrence.selected = FormulaN.ex x B)
      (Gamma Delta : LCS.Finset (FormulaN L)) :
      G2nnfPermutationLowerRuleView (.exSubRight A occurrence x B t hSelected Gamma Delta)

/-- Which exact premise occurrence of the lower rule contains the upper
quantifier occurrence. -/
@[blueprint "chap7__lemma_7_4_2"]
inductive G2nnfPremiseChoice where
  | only
  | left
  | right
deriving DecidableEq

end LCS.Herbrand.NNFHauptsatz.Theorem
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
namespace LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree
open LCS.Herbrand.NNFHauptsatz.G2nnfRule
namespace G2nnfPermutationLowerRuleView

/-- Every core inference with at least one premise has a lower-rule view.
In particular, no quantifier or cut application is excluded from Definition 7.3.2. -/
@[blueprint "chap7__definition_7_3_2"]
def ofHasPremise {L : Language} [DecidableEq (FormulaN L)]
    (rule : G2nnfRuleCore L) (hPremise : 0 < rule.premises.length) :
    G2nnfPermutationLowerRuleView rule :=
  match rule with
  | .axiomPosId .. | .axiomNegId .. | .axiomCompRight .. | .axiomCompLeft .. => by
      simp [G2nnfRuleCore.premises] at hPremise
  | .weakLeft A Gamma Delta => .weakLeft A Gamma Delta
  | .weakRight A Gamma Delta => .weakRight A Gamma Delta
  | .conjLeft1 A B Gamma Delta => .conjLeft1 A B Gamma Delta
  | .conjLeft2 A B Gamma Delta => .conjLeft2 A B Gamma Delta
  | .conjRight A B Gamma Delta => .conjRight A B Gamma Delta
  | .disjLeft A B Gamma Delta => .disjLeft A B Gamma Delta
  | .disjRight1 A B Gamma Delta => .disjRight1 A B Gamma Delta
  | .disjRight2 A B Gamma Delta => .disjRight2 A B Gamma Delta
  | .cut A Lambda Theta Gamma Delta => .cut A Lambda Theta Gamma Delta
  | .allSubLeft A occurrence x B t hSelected Gamma Delta =>
      .allSubLeft A occurrence x B t hSelected Gamma Delta
  | .allSubRight A occurrence x B y hSelected Gamma Delta =>
      .allSubRight A occurrence x B y hSelected Gamma Delta
  | .exSubLeft A occurrence x B y hSelected Gamma Delta =>
      .exSubLeft A occurrence x B y hSelected Gamma Delta
  | .exSubRight A occurrence x B t hSelected Gamma Delta =>
      .exSubRight A occurrence x B t hSelected Gamma Delta

/-- The formula occurrence contributed by the selected premise of the lower
rule. Quantifier premises contribute the formula with the selected subformula
instantiated; cut contributes its cut formula on the selected premise side.
Weakening premises contribute no focused formula;
the quantifier principal must then be inherited from the raw context.  Invalid
arity/choice combinations return `none`, but cannot arise in
`G2nnfSelectedPremiseOccurrence` because its tree constructors carry the exact
premise-length equation. -/
@[blueprint "chap7__lemma_7_4_3", blueprint "chap7__lemma_7_4_2"]
def selectedFocus {L : Language} {rule : G2nnfRuleCore L}
    (view : G2nnfPermutationLowerRuleView rule)
    (choice : G2nnfPremiseChoice) :
    Option (G2nnfSequentSide × FormulaN L) :=
  match view, choice with
  | .weakLeft _ _ _, _ => none
  | .weakRight _ _ _, _ => none
  | .conjLeft1 A _ _ _, .only => some (.left, A)
  | .conjLeft2 _ B _ _, .only => some (.left, B)
  | .conjRight A _ _ _, .left => some (.right, A)
  | .conjRight _ B _ _, .right => some (.right, B)
  | .disjLeft A _ _ _, .left => some (.left, A)
  | .disjLeft _ B _ _, .right => some (.left, B)
  | .disjRight1 A _ _ _, .only => some (.right, A)
  | .disjRight2 _ B _ _, .only => some (.right, B)
  | .allSubLeft _ occurrence x B t _ _ _, .only =>
      some (.left, occurrence.replace (formulaSubstN B t x))
  | .allSubRight _ occurrence x B y _ _ _, .only =>
      some (.right, occurrence.replace (formulaSubstN B (.var y) x))
  | .exSubLeft _ occurrence x B y _ _ _, .only =>
      some (.left, occurrence.replace (formulaSubstN B (.var y) x))
  | .exSubRight _ occurrence x B t _ _ _, .only =>
      some (.right, occurrence.replace (formulaSubstN B t x))
  | .cut A _ _ _ _, .left => some (.right, A)
  | .cut A _ _ _ _, .right => some (.left, A)
  | _, _ => none

/-- The principal formula in the lower conclusion. Quantifier rules return
the ambient formula containing their selected quantified subformula. Weakening
and cut have no logical principal formula in the conclusion; the cut formula
is exposed by `selectedFocus` on either selected premise. -/
@[blueprint "chap7__lemma_7_4_3", blueprint "chap7__lemma_7_4_2"]
def principal {L : Language} {rule : G2nnfRuleCore L}
    (view : G2nnfPermutationLowerRuleView rule) :
    Option (G2nnfSequentSide × FormulaN L) :=
  match view with
  | .weakLeft _ _ _ => none
  | .weakRight _ _ _ => none
  | .conjLeft1 A B _ _ => some (.left, .conj A B)
  | .conjLeft2 A B _ _ => some (.left, .conj A B)
  | .conjRight A B _ _ => some (.right, .conj A B)
  | .disjLeft A B _ _ => some (.left, .disj A B)
  | .disjRight1 A B _ _ => some (.right, .disj A B)
  | .disjRight2 A B _ _ => some (.right, .disj A B)
  | .allSubLeft A _ _ _ _ _ _ _ => some (.left, A)
  | .allSubRight A _ _ _ _ _ _ _ => some (.right, A)
  | .exSubLeft A _ _ _ _ _ _ _ => some (.left, A)
  | .exSubRight A _ _ _ _ _ _ _ => some (.right, A)
  | .cut _ _ _ _ _ => none

/-- Map the formula operands of a propositional or weakening rule.
This Lemma 7.4.2 operation returns `none` for quantifier and cut lower rules;
quantifier occurrence transport and cut's two contexts are handled separately. -/
@[blueprint "chap7__lemma_7_4_2"]
def mapFormulae {L : Language} {rule : G2nnfRuleCore L}
    (view : G2nnfPermutationLowerRuleView rule)
    (f : FormulaN L → FormulaN L)
    (Gamma Delta : LCS.Finset (FormulaN L)) : Option (G2nnfRuleCore L) :=
  match view with
  | .weakLeft A _ _ => some (.weakLeft (f A) Gamma Delta)
  | .weakRight A _ _ => some (.weakRight (f A) Gamma Delta)
  | .conjLeft1 A B _ _ => some (.conjLeft1 (f A) (f B) Gamma Delta)
  | .conjLeft2 A B _ _ => some (.conjLeft2 (f A) (f B) Gamma Delta)
  | .conjRight A B _ _ => some (.conjRight (f A) (f B) Gamma Delta)
  | .disjLeft A B _ _ => some (.disjLeft (f A) (f B) Gamma Delta)
  | .disjRight1 A B _ _ => some (.disjRight1 (f A) (f B) Gamma Delta)
  | .disjRight2 A B _ _ => some (.disjRight2 (f A) (f B) Gamma Delta)
  | .allSubLeft .. | .allSubRight .. | .exSubLeft .. | .exSubRight .. | .cut .. => none

/-- Retain all rule operands and dependent quantifier occurrences while
replacing the first pair of side contexts. Cut retains its independent second
pair; the general permutation relation supplies both pairs for cut. -/
@[blueprint "chap7__definition_7_3_2"]
def withContexts {L : Language} {rule : G2nnfRuleCore L}
    (view : G2nnfPermutationLowerRuleView rule)
    (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L :=
  match view with
  | .weakLeft A _ _ => .weakLeft A Gamma Delta
  | .weakRight A _ _ => .weakRight A Gamma Delta
  | .conjLeft1 A B _ _ => .conjLeft1 A B Gamma Delta
  | .conjLeft2 A B _ _ => .conjLeft2 A B Gamma Delta
  | .conjRight A B _ _ => .conjRight A B Gamma Delta
  | .disjLeft A B _ _ => .disjLeft A B Gamma Delta
  | .disjRight1 A B _ _ => .disjRight1 A B Gamma Delta
  | .disjRight2 A B _ _ => .disjRight2 A B Gamma Delta
  | .allSubLeft A occurrence x B t hSelected _ _ =>
      .allSubLeft A occurrence x B t hSelected Gamma Delta
  | .allSubRight A occurrence x B y hSelected _ _ =>
      .allSubRight A occurrence x B y hSelected Gamma Delta
  | .exSubLeft A occurrence x B y hSelected _ _ =>
      .exSubLeft A occurrence x B y hSelected Gamma Delta
  | .exSubRight A occurrence x B t hSelected _ _ =>
      .exSubRight A occurrence x B t hSelected Gamma Delta
  | .cut A Lambda Theta _ _ => .cut A Lambda Theta Gamma Delta

/-- Instantiate the selected propositional premise formula, preserving the
other branch. This Lemma 7.4.2 operation returns `none` for lower quantifier
rules and cut, which require dependent occurrence transport or cut instances. -/
@[blueprint "chap7__lemma_7_4_2"]
def instantiateSelected {L : Language} {R₁ R₂ : G2nnfRuleCore L}
    (lower : G2nnfPermutationLowerRuleView R₂)
    (quantifier : G2nnfQuantifierRuleView R₁)
    (choice : G2nnfPremiseChoice)
    (Gamma Delta : LCS.Finset (FormulaN L)) : Option (G2nnfRuleCore L) :=
  match lower, choice with
  | .weakLeft A _ _, _ =>
      some (.weakLeft A Gamma Delta)
  | .weakRight A _ _, _ =>
      some (.weakRight A Gamma Delta)
  | .conjLeft1 A B _ _, .only =>
      some (.conjLeft1 quantifier.premisePrincipal B Gamma Delta)
  | .conjLeft1 A B _ _, _ =>
      some (.conjLeft1 A B Gamma Delta)
  | .conjLeft2 A B _ _, .only =>
      some (.conjLeft2 A quantifier.premisePrincipal Gamma Delta)
  | .conjLeft2 A B _ _, _ =>
      some (.conjLeft2 A B Gamma Delta)
  | .conjRight A B _ _, .left =>
      some (.conjRight quantifier.premisePrincipal B Gamma Delta)
  | .conjRight A B _ _, .right =>
      some (.conjRight A quantifier.premisePrincipal Gamma Delta)
  | .conjRight A B _ _, .only =>
      some (.conjRight A B Gamma Delta)
  | .disjLeft A B _ _, .left =>
      some (.disjLeft quantifier.premisePrincipal B Gamma Delta)
  | .disjLeft A B _ _, .right =>
      some (.disjLeft A quantifier.premisePrincipal Gamma Delta)
  | .disjLeft A B _ _, .only =>
      some (.disjLeft A B Gamma Delta)
  | .disjRight1 A B _ _, .only =>
      some (.disjRight1 quantifier.premisePrincipal B Gamma Delta)
  | .disjRight1 A B _ _, _ =>
      some (.disjRight1 A B Gamma Delta)
  | .disjRight2 A B _ _, .only =>
      some (.disjRight2 A quantifier.premisePrincipal Gamma Delta)
  | .disjRight2 A B _ _, _ =>
      some (.disjRight2 A B Gamma Delta)
  | .allSubLeft .., _ | .allSubRight .., _
  | .exSubLeft .., _ | .exSubRight .., _ | .cut .., _ => none

/-- Total selected-premise instantiation on Lemma 7.4.2's propositional or
weakening domain. The scope evidence excludes quantifier rules and cut. -/
@[blueprint "chap7__lemma_7_4_2"]
def instantiateSelectedOfPropositional {L : Language} {R₁ R₂ : G2nnfRuleCore L}
    (lower : G2nnfPermutationLowerRuleView R₂)
    (hLower : R₂.isPropositionalRule ∨ R₂.isWeakening)
    (quantifier : G2nnfQuantifierRuleView R₁)
    (choice : G2nnfPremiseChoice)
    (Gamma Delta : LCS.Finset (FormulaN L)) : G2nnfRuleCore L :=
  match lower, choice with
  | .weakLeft A _ _, _ => .weakLeft A Gamma Delta
  | .weakRight A _ _, _ => .weakRight A Gamma Delta
  | .conjLeft1 A B _ _, .only =>
      .conjLeft1 quantifier.premisePrincipal B Gamma Delta
  | .conjLeft1 A B _ _, _ => .conjLeft1 A B Gamma Delta
  | .conjLeft2 A B _ _, .only =>
      .conjLeft2 A quantifier.premisePrincipal Gamma Delta
  | .conjLeft2 A B _ _, _ => .conjLeft2 A B Gamma Delta
  | .conjRight A B _ _, .left =>
      .conjRight quantifier.premisePrincipal B Gamma Delta
  | .conjRight A B _ _, .right =>
      .conjRight A quantifier.premisePrincipal Gamma Delta
  | .conjRight A B _ _, .only => .conjRight A B Gamma Delta
  | .disjLeft A B _ _, .left =>
      .disjLeft quantifier.premisePrincipal B Gamma Delta
  | .disjLeft A B _ _, .right =>
      .disjLeft A quantifier.premisePrincipal Gamma Delta
  | .disjLeft A B _ _, .only => .disjLeft A B Gamma Delta
  | .disjRight1 A B _ _, .only =>
      .disjRight1 quantifier.premisePrincipal B Gamma Delta
  | .disjRight1 A B _ _, _ => .disjRight1 A B Gamma Delta
  | .disjRight2 A B _ _, .only =>
      .disjRight2 A quantifier.premisePrincipal Gamma Delta
  | .disjRight2 A B _ _, _ => .disjRight2 A B Gamma Delta
  | .allSubLeft .., _ | .allSubRight .., _
  | .exSubLeft .., _ | .exSubRight .., _ | .cut .., _ => by
      simp [G2nnfRuleCore.isPropositionalRule, G2nnfRuleCore.isWeakening] at hLower

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.RuleOccurrences
/-- Logical principal of the occurrence-focused propositional lower-rule image.
This Lemma 7.4.2 helper returns `none` for quantifier and cut lower rules, whose
permutation requires separate occurrence transport. -/
def instantiatedPrincipal {L : Language} {R₁ R₂ : G2nnfRuleCore L}
    (lower : G2nnfPermutationLowerRuleView R₂)
    (quantifier : G2nnfQuantifierRuleView R₁)
    (choice : G2nnfPremiseChoice) :
    Option (G2nnfSequentSide × FormulaN L) :=
  match lower, choice with
  | .weakLeft _ _ _, _ => none
  | .weakRight _ _ _, _ => none
  | .conjLeft1 _ B _ _, .only =>
      some (.left, .conj quantifier.premisePrincipal B)
  | .conjLeft1 A B _ _, _ => some (.left, .conj A B)
  | .conjLeft2 A _ _ _, .only =>
      some (.left, .conj A quantifier.premisePrincipal)
  | .conjLeft2 A B _ _, _ => some (.left, .conj A B)
  | .conjRight _ B _ _, .left =>
      some (.right, .conj quantifier.premisePrincipal B)
  | .conjRight A _ _ _, .right =>
      some (.right, .conj A quantifier.premisePrincipal)
  | .conjRight A B _ _, .only => some (.right, .conj A B)
  | .disjLeft _ B _ _, .left =>
      some (.left, .disj quantifier.premisePrincipal B)
  | .disjLeft A _ _ _, .right =>
      some (.left, .disj A quantifier.premisePrincipal)
  | .disjLeft A B _ _, .only => some (.left, .disj A B)
  | .disjRight1 _ B _ _, .only =>
      some (.right, .disj quantifier.premisePrincipal B)
  | .disjRight1 A B _ _, _ => some (.right, .disj A B)
  | .disjRight2 A _ _ _, .only =>
      some (.right, .disj A quantifier.premisePrincipal)
  | .disjRight2 A B _ _, _ => some (.right, .disj A B)
  | .allSubLeft .., _ | .allSubRight .., _
  | .exSubLeft .., _ | .exSubRight .., _ | .cut .., _ => none

/-- An exact lift of one selected occurrence into a surrounding connective,
including the invariant that the selected quantified formula is unchanged. -/
@[blueprint "chap7__lemma_7_4_3"]
structure G2nnfFocusedOccurrenceLift {L : Language}
    (target selected : FormulaN L) where
  occurrence : MaxQuantifierOccurrence target
  selected_eq : occurrence.selected = selected
attribute [blueprint "chap7__lemma_7_4_3"] _root_.LCS.Herbrand.NNFHauptsatz.Theorem.G2nnfPermutationLowerRuleView.G2nnfFocusedOccurrenceLift.occurrence

attribute [blueprint "chap7__lemma_7_4_3"] _root_.LCS.Herbrand.NNFHauptsatz.Theorem.G2nnfPermutationLowerRuleView.G2nnfFocusedOccurrenceLift.selected_eq


/-- Lift a selected maximal occurrence through the exact connective branch
identified by a focused lower premise. This Lemma 7.4.2 connective helper
returns `none` for quantifier rules and cut: maximal occurrences do not in
general lift through a quantifier, and a cut removes its cut formula. -/
@[blueprint "chap7__lemma_7_4_3"]
def liftFocusedOccurrence {L : Language} {R₂ : G2nnfRuleCore L}
    (lower : G2nnfPermutationLowerRuleView R₂)
    (choice : G2nnfPremiseChoice)
    {side : G2nnfSequentSide} {selected target : FormulaN L}
    (hFocus : lower.selectedFocus choice = some (side, selected))
    (hPrincipal : lower.principal = some (side, target))
    (occurrence : MaxQuantifierOccurrence selected) :
    Option (G2nnfFocusedOccurrenceLift target occurrence.selected) :=
  match lower, choice with
  | .weakLeft _ _ _, _ => by simp [selectedFocus] at hFocus
  | .weakRight _ _ _, _ => by simp [selectedFocus] at hFocus
  | .conjLeft1 A B _ _, .only => by
      simp only [selectedFocus, Option.some.injEq, Prod.mk.injEq] at hFocus
      simp only [principal, Option.some.injEq, Prod.mk.injEq] at hPrincipal
      rcases hFocus with ⟨rfl, rfl⟩
      rcases hPrincipal with ⟨_, rfl⟩
      exact some ⟨.conjLeft occurrence B, rfl⟩
  | .conjLeft1 _ _ _ _, .left => by simp [selectedFocus] at hFocus
  | .conjLeft1 _ _ _ _, .right => by simp [selectedFocus] at hFocus
  | .conjLeft2 A B _ _, .only => by
      simp only [selectedFocus, Option.some.injEq, Prod.mk.injEq] at hFocus
      simp only [principal, Option.some.injEq, Prod.mk.injEq] at hPrincipal
      rcases hFocus with ⟨rfl, rfl⟩
      rcases hPrincipal with ⟨_, rfl⟩
      exact some ⟨.conjRight A occurrence, rfl⟩
  | .conjLeft2 _ _ _ _, .left => by simp [selectedFocus] at hFocus
  | .conjLeft2 _ _ _ _, .right => by simp [selectedFocus] at hFocus
  | .conjRight A B _ _, .left => by
      simp only [selectedFocus, Option.some.injEq, Prod.mk.injEq] at hFocus
      simp only [principal, Option.some.injEq, Prod.mk.injEq] at hPrincipal
      rcases hFocus with ⟨rfl, rfl⟩
      rcases hPrincipal with ⟨_, rfl⟩
      exact some ⟨.conjLeft occurrence B, rfl⟩
  | .conjRight A B _ _, .right => by
      simp only [selectedFocus, Option.some.injEq, Prod.mk.injEq] at hFocus
      simp only [principal, Option.some.injEq, Prod.mk.injEq] at hPrincipal
      rcases hFocus with ⟨rfl, rfl⟩
      rcases hPrincipal with ⟨_, rfl⟩
      exact some ⟨.conjRight A occurrence, rfl⟩
  | .conjRight _ _ _ _, .only => by simp [selectedFocus] at hFocus
  | .disjLeft A B _ _, .left => by
      simp only [selectedFocus, Option.some.injEq, Prod.mk.injEq] at hFocus
      simp only [principal, Option.some.injEq, Prod.mk.injEq] at hPrincipal
      rcases hFocus with ⟨rfl, rfl⟩
      rcases hPrincipal with ⟨_, rfl⟩
      exact some ⟨.disjLeft occurrence B, rfl⟩
  | .disjLeft A B _ _, .right => by
      simp only [selectedFocus, Option.some.injEq, Prod.mk.injEq] at hFocus
      simp only [principal, Option.some.injEq, Prod.mk.injEq] at hPrincipal
      rcases hFocus with ⟨rfl, rfl⟩
      rcases hPrincipal with ⟨_, rfl⟩
      exact some ⟨.disjRight A occurrence, rfl⟩
  | .disjLeft _ _ _ _, .only => by simp [selectedFocus] at hFocus
  | .disjRight1 A B _ _, .only => by
      simp only [selectedFocus, Option.some.injEq, Prod.mk.injEq] at hFocus
      simp only [principal, Option.some.injEq, Prod.mk.injEq] at hPrincipal
      rcases hFocus with ⟨rfl, rfl⟩
      rcases hPrincipal with ⟨_, rfl⟩
      exact some ⟨.disjLeft occurrence B, rfl⟩
  | .disjRight1 _ _ _ _, .left => by simp [selectedFocus] at hFocus
  | .disjRight1 _ _ _ _, .right => by simp [selectedFocus] at hFocus
  | .disjRight2 A B _ _, .only => by
      simp only [selectedFocus, Option.some.injEq, Prod.mk.injEq] at hFocus
      simp only [principal, Option.some.injEq, Prod.mk.injEq] at hPrincipal
      rcases hFocus with ⟨rfl, rfl⟩
      rcases hPrincipal with ⟨_, rfl⟩
      exact some ⟨.disjRight A occurrence, rfl⟩
  | .disjRight2 _ _ _ _, .left => by simp [selectedFocus] at hFocus
  | .disjRight2 _ _ _ _, .right => by simp [selectedFocus] at hFocus
  | .allSubLeft .., _ | .allSubRight .., _
  | .exSubLeft .., _ | .exSubRight .., _ | .cut .., _ => none

end G2nnfPermutationLowerRuleView
end LCS.Herbrand.NNFHauptsatz.Theorem
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
namespace LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree
open LCS.Herbrand.NNFHauptsatz.G2nnfRule

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Stored antecedent/succedent side contexts. For cut these are the first
premise's frame; the independent second frame remains in the rule itself. -/
def g2nnfRuleSideContexts {L : Language} : G2nnfRuleCore L →
    LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)
  | .axiomPosId _ _ Gamma Delta | .axiomNegId _ _ Gamma Delta
  | .axiomCompRight _ _ Gamma Delta | .axiomCompLeft _ _ Gamma Delta
  | .weakLeft _ Gamma Delta | .weakRight _ Gamma Delta
  | .conjLeft1 _ _ Gamma Delta | .conjLeft2 _ _ Gamma Delta
  | .conjRight _ _ Gamma Delta | .disjLeft _ _ Gamma Delta
  | .disjRight1 _ _ Gamma Delta | .disjRight2 _ _ Gamma Delta
  | .cut _ _ _ Gamma Delta
  | .allSubLeft _ _ _ _ _ _ Gamma Delta
  | .allSubRight _ _ _ _ _ _ Gamma Delta
  | .exSubLeft _ _ _ _ _ _ Gamma Delta
  | .exSubRight _ _ _ _ _ _ Gamma Delta => (Gamma, Delta)
/-- Exact evidence that `node` is a one-premise application of `rule`, with
its stored contexts, bare admission, side conditions and premise tree
retained in the indexed rule and constructor data. -/
@[blueprint "chap7__lemma_7_4_2"]
inductive G2nnfOnePremiseApplication {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] (rule : G2nnfRuleCore L) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfProofTree hL Γ Δ → Type where
  | of (hAdmit : rule.BareAtomicAxiom)
      (hPrem : (rule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions rule)
      (sub : G2nnfProofTree hL
        ((rule.premises)[0]'(by omega)).1
        ((rule.premises)[0]'(by omega)).2) :
      G2nnfOnePremiseApplication rule
        (.onePremise rule hAdmit hPrem hSC sub)
end LCS.Herbrand.NNFHauptsatz.Theorem
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
namespace LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree
open LCS.Herbrand.NNFHauptsatz.G2nnfRule
namespace G2nnfOnePremiseApplication

/-- Raw antecedent context of the exact one-premise application. -/
@[blueprint "chap7__lemma_7_4_2"]
def rawGamma {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {rule : G2nnfRuleCore L} {Γ Δ : LCS.Finset (FormulaN L)}
    {node : G2nnfProofTree hL Γ Δ} :
    G2nnfOnePremiseApplication rule node →
      LCS.Finset (FormulaN L)
  | _ => (g2nnfRuleSideContexts rule).1
/-- Raw succedent context of the exact one-premise application. -/
@[blueprint "chap7__lemma_7_4_2"]
def rawDelta {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {rule : G2nnfRuleCore L} {Γ Δ : LCS.Finset (FormulaN L)}
    {node : G2nnfProofTree hL Γ Δ} :
    G2nnfOnePremiseApplication rule node →
      LCS.Finset (FormulaN L)
  | _ => (g2nnfRuleSideContexts rule).2
end G2nnfOnePremiseApplication
end LCS.Herbrand.NNFHauptsatz.Theorem
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
namespace LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree
open LCS.Herbrand.NNFHauptsatz.G2nnfRule

/-- Exact evidence that a node applies a fixed rule with its actual arity.
This is used for target lower-rule occurrences, which may have one or two
premises. -/
@[blueprint "chap7__lemma_7_4_2"]
inductive G2nnfRuleApplication {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] (rule : G2nnfRuleCore L) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfProofTree hL Γ Δ → Type where
  | one (hAdmit : rule.BareAtomicAxiom)
      (hPrem : (rule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions rule)
      (sub : G2nnfProofTree hL
        ((rule.premises)[0]'(by omega)).1
        ((rule.premises)[0]'(by omega)).2) :
      G2nnfRuleApplication rule
        (.onePremise rule hAdmit hPrem hSC sub)
  | two (hAdmit : rule.BareAtomicAxiom)
      (hPrem : (rule.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions rule)
      (sub1 : G2nnfProofTree hL
        ((rule.premises)[0]'(by omega)).1
        ((rule.premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        ((rule.premises)[1]'(by omega)).1
        ((rule.premises)[1]'(by omega)).2) :
      G2nnfRuleApplication rule
        (.twoPremise rule hAdmit hPrem hSC sub1 sub2)
/-- The exact premise frontier hidden in a one-premise application witness. -/
@[blueprint "chap7__lemma_7_4_2"]
inductive G2nnfOnePremiseFrontier {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] {rule : G2nnfRuleCore L} :
    {Γnode Δnode : LCS.Finset (FormulaN L)} →
    {node : G2nnfProofTree hL Γnode Δnode} →
    G2nnfOnePremiseApplication rule node →
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfProofTree hL Γ Δ → Type where
  | of (hAdmit : rule.BareAtomicAxiom)
      (hPrem : (rule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions rule)
      (sub : G2nnfProofTree hL
        ((rule.premises)[0]'(by omega)).1
        ((rule.premises)[0]'(by omega)).2) :
      G2nnfOnePremiseFrontier
        (G2nnfOnePremiseApplication.of hAdmit hPrem hSC sub) sub
end LCS.Herbrand.NNFHauptsatz.Theorem
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
namespace LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree
open LCS.Herbrand.NNFHauptsatz.G2nnfRule
namespace G2nnfOnePremiseFrontier

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Exact one-step path from an application to the premise frontier exposed
by its witness. -/
def path {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {rule : G2nnfRuleCore L}
    {Γnode Δnode Γ Δ : LCS.Finset (FormulaN L)}
    {node : G2nnfProofTree hL Γnode Δnode}
    {application : G2nnfOnePremiseApplication rule node}
    {sub : G2nnfProofTree hL Γ Δ}
    (frontier : G2nnfOnePremiseFrontier application sub) :
    RootToNodePath node sub :=
  match frontier with
  | .of hAdmit hPrem hSC sub =>
    .onePremise rule hAdmit hPrem hSC sub (.root sub)
end G2nnfOnePremiseFrontier
end LCS.Herbrand.NNFHauptsatz.Theorem
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
namespace LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree
open LCS.Herbrand.NNFHauptsatz.G2nnfRule

/-- Proof-relevant evidence that every rule strictly between the start and
target nodes of an exact path is a weakening.  A root path has no intermediate
rules.  There are intentionally no two-premise constructors: every G2nnf
weakening is one-premise, so a binary node cannot lie in the structural section
`ST`. -/
@[blueprint "chap7__lemma_7_4_2"]
inductive G2nnfWeakeningOnlyPath {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] :
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)} →
    {root : G2nnfProofTree hL Γroot Δroot} →
    {node : G2nnfProofTree hL Γnode Δnode} →
    (path : RootToNodePath root node) → Type where
  | root {Γ Δ : LCS.Finset (FormulaN L)}
      (T : G2nnfProofTree hL Γ Δ) :
      G2nnfWeakeningOnlyPath (.root T)
  | onePremise (rule : G2nnfRuleCore L)
      (hAdmit : rule.BareAtomicAxiom)
      (hPrem : (rule.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions rule)
      (sub : G2nnfProofTree hL
        ((rule.premises)[0]'(by omega)).1
        ((rule.premises)[0]'(by omega)).2)
      {Γnode Δnode : LCS.Finset (FormulaN L)}
      {node : G2nnfProofTree hL Γnode Δnode}
      {path : RootToNodePath sub node}
      (hWeak : rule.isWeakening)
      (rest : G2nnfWeakeningOnlyPath path) :
      G2nnfWeakeningOnlyPath
        (.onePremise rule hAdmit hPrem hSC sub path)
/-- An exact occurrence of a lower `R₂` application together with the selected
premise occurrence through which the upper quantifier `R₁` is reached.  The
constructors use `R₂` directly, rather than storing a node whose rule is merely
equal to `R₂`. -/
@[blueprint "chap7__lemma_7_4_2"]
inductive G2nnfSelectedPremiseOccurrence {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    (root : G2nnfProofTree hL Γroot Δroot) (R₂ : G2nnfRuleCore L) :
    {Γprem Δprem : LCS.Finset (FormulaN L)} →
    G2nnfProofTree hL Γprem Δprem → Type where
  | one (hAdmit : R₂.BareAtomicAxiom)
      (hPrem : (R₂.premises).length = 1)
      (hSC : G2nnfRuleCore.SideConditions R₂)
      (sub : G2nnfProofTree hL
        ((R₂.premises)[0]'(by omega)).1
        ((R₂.premises)[0]'(by omega)).2)
      (path : RootToNodePath root
        (.onePremise R₂ hAdmit hPrem hSC sub)) :
      G2nnfSelectedPremiseOccurrence root R₂ sub
  | left (hAdmit : R₂.BareAtomicAxiom)
      (hPrem : (R₂.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions R₂)
      (sub1 : G2nnfProofTree hL
        ((R₂.premises)[0]'(by omega)).1
        ((R₂.premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        ((R₂.premises)[1]'(by omega)).1
        ((R₂.premises)[1]'(by omega)).2)
      (path : RootToNodePath root
        (.twoPremise R₂ hAdmit hPrem hSC sub1 sub2)) :
      G2nnfSelectedPremiseOccurrence root R₂ sub1
  | right (hAdmit : R₂.BareAtomicAxiom)
      (hPrem : (R₂.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions R₂)
      (sub1 : G2nnfProofTree hL
        ((R₂.premises)[0]'(by omega)).1
        ((R₂.premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        ((R₂.premises)[1]'(by omega)).1
        ((R₂.premises)[1]'(by omega)).2)
      (path : RootToNodePath root
        (.twoPremise R₂ hAdmit hPrem hSC sub1 sub2)) :
      G2nnfSelectedPremiseOccurrence root R₂ sub2
/-- The exact non-selected frontier of a binary lower application.  There is
no constructor for a one-premise application. -/
@[blueprint "chap7__lemma_7_4_2"]
inductive G2nnfOtherPremiseFrontier {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot} {R₂ : G2nnfRuleCore L} :
    {Γselected Δselected : LCS.Finset (FormulaN L)} →
    {selectedTree : G2nnfProofTree hL Γselected Δselected} →
    G2nnfSelectedPremiseOccurrence root R₂ selectedTree →
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfProofTree hL Γ Δ → Type where
  | ofLeft (hAdmit : R₂.BareAtomicAxiom)
      (hPrem : (R₂.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions R₂)
      (sub1 : G2nnfProofTree hL
        ((R₂.premises)[0]'(by omega)).1
        ((R₂.premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        ((R₂.premises)[1]'(by omega)).1
        ((R₂.premises)[1]'(by omega)).2)
      (path : RootToNodePath root
        (.twoPremise R₂ hAdmit hPrem hSC sub1 sub2)) :
      G2nnfOtherPremiseFrontier
        (G2nnfSelectedPremiseOccurrence.left
          hAdmit hPrem hSC sub1 sub2 path) sub2
  | ofRight (hAdmit : R₂.BareAtomicAxiom)
      (hPrem : (R₂.premises).length = 2)
      (hSC : G2nnfRuleCore.SideConditions R₂)
      (sub1 : G2nnfProofTree hL
        ((R₂.premises)[0]'(by omega)).1
        ((R₂.premises)[0]'(by omega)).2)
      (sub2 : G2nnfProofTree hL
        ((R₂.premises)[1]'(by omega)).1
        ((R₂.premises)[1]'(by omega)).2)
      (path : RootToNodePath root
        (.twoPremise R₂ hAdmit hPrem hSC sub1 sub2)) :
      G2nnfOtherPremiseFrontier
        (G2nnfSelectedPremiseOccurrence.right
          hAdmit hPrem hSC sub1 sub2 path) sub1
end LCS.Herbrand.NNFHauptsatz.Theorem
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
namespace LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree
open LCS.Herbrand.NNFHauptsatz.G2nnfRule
namespace G2nnfOtherPremiseFrontier

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Exact ambient path to the non-selected binary frontier.  The constructor
choice is complementary to the selected premise and remains
occurrence-sensitive even when both subtree values are equal. -/
def path {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {GammaRoot DeltaRoot GammaSelected DeltaSelected Gamma Delta :
      LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL GammaRoot DeltaRoot}
    {R₂ : G2nnfRuleCore L}
    {selectedTree : G2nnfProofTree hL GammaSelected DeltaSelected}
    {selected :
      G2nnfSelectedPremiseOccurrence root R₂ selectedTree}
    {other : G2nnfProofTree hL Gamma Delta}
    (frontier : G2nnfOtherPremiseFrontier selected other) :
    RootToNodePath root other :=
  match frontier with
  | .ofLeft hAdmit hPrem hSC sub1 sub2 applicationPath =>
      applicationPath.trans
        (.rightPremise R₂ hAdmit hPrem hSC sub1 sub2 (.root sub2))
  | .ofRight hAdmit hPrem hSC sub1 sub2 applicationPath =>
      applicationPath.trans
        (.leftPremise R₂ hAdmit hPrem hSC sub1 sub2 (.root sub1))
-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Exact node occurrence of the non-selected binary frontier. -/
def occurrence {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {GammaRoot DeltaRoot GammaSelected DeltaSelected Gamma Delta :
      LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL GammaRoot DeltaRoot}
    {R₂ : G2nnfRuleCore L}
    {selectedTree : G2nnfProofTree hL GammaSelected DeltaSelected}
    {selected :
      G2nnfSelectedPremiseOccurrence root R₂ selectedTree}
    {other : G2nnfProofTree hL Gamma Delta}
    (frontier : G2nnfOtherPremiseFrontier selected other) :
    NodeOccurrence root Gamma Delta :=
  ⟨other, frontier.path⟩


end G2nnfOtherPremiseFrontier
end LCS.Herbrand.NNFHauptsatz.Theorem
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
namespace LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree
open LCS.Herbrand.NNFHauptsatz.G2nnfRule

/-- An exact located application of a fixed rule. -/
@[blueprint "chap7__lemma_7_4_2"]
structure G2nnfLocatedRuleApplication {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    (root : G2nnfProofTree hL Γroot Δroot) (rule : G2nnfRuleCore L) where
  Γ : LCS.Finset (FormulaN L)
  Δ : LCS.Finset (FormulaN L)
  node : G2nnfProofTree hL Γ Δ
  path : RootToNodePath root node
  application : G2nnfRuleApplication rule node
end LCS.Herbrand.NNFHauptsatz.Theorem
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
namespace LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree
open LCS.Herbrand.NNFHauptsatz.G2nnfRule
namespace G2nnfSelectedPremiseOccurrence

/-- Raw antecedent context of the exact lower-rule application. -/
@[blueprint "chap7__lemma_7_4_2"]
def rawGamma {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γroot Δroot Γprem Δprem : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot} {R₂ : G2nnfRuleCore L}
    {premise : G2nnfProofTree hL Γprem Δprem} :
    G2nnfSelectedPremiseOccurrence root R₂ premise →
      LCS.Finset (FormulaN L)
  | .right .. =>
    match R₂ with
    | .cut _ Lambda Theta _ _ => Lambda
    | _ => (g2nnfRuleSideContexts R₂).1
  | _ => (g2nnfRuleSideContexts R₂).1
/-- Raw succedent context of the exact lower-rule application. -/
@[blueprint "chap7__lemma_7_4_2"]
def rawDelta {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γroot Δroot Γprem Δprem : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot} {R₂ : G2nnfRuleCore L}
    {premise : G2nnfProofTree hL Γprem Δprem} :
    G2nnfSelectedPremiseOccurrence root R₂ premise →
      LCS.Finset (FormulaN L)
  | .right .. =>
    match R₂ with
    | .cut _ Lambda Theta _ _ => Theta
    | _ => (g2nnfRuleSideContexts R₂).2
  | _ => (g2nnfRuleSideContexts R₂).2
/-- The exact premise choice retained by the occurrence constructor. -/
@[blueprint "chap7__lemma_7_4_2"]
def choice {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γroot Δroot Γprem Δprem : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot} {R₂ : G2nnfRuleCore L}
    {premise : G2nnfProofTree hL Γprem Δprem} :
    G2nnfSelectedPremiseOccurrence root R₂ premise →
      G2nnfPremiseChoice
  | .one _ _ _ _ _ => .only
  | .left _ _ _ _ _ _ => .left
  | .right _ _ _ _ _ _ => .right
-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.RuleOccurrences
/-- The exact ambient path to the selected premise. -/
def premisePath {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γroot Δroot Γprem Δprem : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot} {R₂ : G2nnfRuleCore L}
    {premise : G2nnfProofTree hL Γprem Δprem}
    (selected : G2nnfSelectedPremiseOccurrence root R₂ premise) :
    RootToNodePath root premise :=
  match selected with
  | .one hAdmit hPrem hSC sub path =>
      path.trans
        (.onePremise R₂ hAdmit hPrem hSC sub (.root sub))
  | .left hAdmit hPrem hSC sub1 sub2 path =>
      path.trans
        (.leftPremise R₂ hAdmit hPrem hSC sub1 sub2 (.root sub1))
  | .right hAdmit hPrem hSC sub1 sub2 path =>
      path.trans
        (.rightPremise R₂ hAdmit hPrem hSC sub1 sub2 (.root sub2))
end G2nnfSelectedPremiseOccurrence
end LCS.Herbrand.NNFHauptsatz.Theorem
end

