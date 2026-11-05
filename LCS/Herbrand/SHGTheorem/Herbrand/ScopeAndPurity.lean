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
import LCS.Herbrand.SHGTheorem.Herbrand.CInstanceCombination
import LCS.Herbrand.SHGTheorem.Herbrand.ClosedSubstitution

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

/-- Equality-system exact existential-left purity step. -/
theorem g2nnfEqExSubLeft_purity_step
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {GammaRoot DeltaRoot : LCS.Finset (FormulaN L)}
    {outer : G2nnfEqProofTree hL GammaRoot DeltaRoot}
    (A B : FormulaN L)
    (occurrence : MaxQuantifierOccurrence A)
    (x y : Nat)
    (hSelected :
      occurrence.selected = FormulaN.ex x B)
    (Gamma Delta : LCS.Finset (FormulaN L))
    (hPrem :
      (G2nnfRuleCore.exSubLeft A occurrence x B y hSelected Gamma Delta).premises.length = 1)
    (hSC :
      G2nnfRuleCore.SideConditions
        (.exSubLeft A occurrence x B y hSelected Gamma Delta))
    (sub : G2nnfEqProofTree hL
      (((G2nnfRuleCore.exSubLeft A occurrence x B y hSelected Gamma Delta).premises)[0]'(by omega)).1
      (((G2nnfRuleCore.exSubLeft A occurrence x B y hSelected Gamma Delta).premises)[0]'(by omega)).2)
    (pathPrefix : G2nnfEqProofTree.RootToNodePath outer
      (.onePremise
        (.exSubLeft A occurrence x B y hSelected Gamma Delta) trivial hPrem hSC sub))
    (hPure :
      isPureVariableProof_G2nnfEqAux outer
        (.onePremise
          (.exSubLeft A occurrence x B y hSelected Gamma Delta) trivial
          hPrem hSC sub)
        pathPrefix) :
    let step : G2nnfEqProofTree.RootToNodePath
        (.onePremise
          (.exSubLeft A occurrence x B y hSelected Gamma Delta) trivial
          hPrem hSC sub)
        sub :=
      .onePremise
        (.exSubLeft A occurrence x B y hSelected Gamma Delta) trivial
        hPrem hSC sub (.root sub)
    g2nnfEqSequentVariableFree y
        (LCS.Finset.insert A Gamma) Delta ∧
      isPureVariableProof_G2nnfEqAux outer sub
        (pathPrefix.trans step) := by
  dsimp only
  let step : G2nnfEqProofTree.RootToNodePath
      (.onePremise
        (.exSubLeft A occurrence x B y hSelected Gamma Delta) trivial
        hPrem hSC sub)
      sub :=
    .onePremise
      (.exSubLeft A occurrence x B y hSelected Gamma Delta) trivial
      hPrem hSC sub (.root sub)
  change
    (g2nnfEqNoFreeBoundOverlap y outer ∧
      g2nnfEqVariableOccursOnlyAlongPath y
        (pathPrefix.trans step)) ∧
      isPureVariableProof_G2nnfEqAux outer sub
        (pathPrefix.trans step) at hPure
  have hSuffix :=
    g2nnfEqVariableOccursOnlyAlongPath_suffix
      y pathPrefix step hPure.1.2
  exact ⟨hSuffix.1, hPure.2⟩

/-- Accumulator form of relevant-eigenvariable freshness for one exact
G2nnf path.  The proof crosses every path constructor.  At a relevant
existential-left step, occurrence-sensitive purity excludes the new
eigenvariable from the current conclusion; relevance and the free-for
side condition then make it live in the premise. -/
private theorem g2nnfRelevantEigenvariables_nodup_live
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {GammaRoot DeltaRoot GammaCur DeltaCur GammaNode DeltaNode :
      LCS.Finset (FormulaN L)}
    (outer : G2nnfProofTree hNoEq GammaRoot DeltaRoot)
    (current : G2nnfProofTree hNoEq GammaCur DeltaCur)
    (pathPrefix : G2nnfProofTree.RootToNodePath outer current)
    (hPure :
      isPureVariableProofG2nnfAux outer current pathPrefix)
    {node : G2nnfProofTree hNoEq GammaNode DeltaNode}
    (path : G2nnfProofTree.RootToNodePath current node)
    (hQuantifier : AllRulesQuantifierOnPath path)
    (variables : List Nat)
    (hNodup : variables.Nodup)
    (hLive :
      AntecedentVariablesLive variables GammaCur) :
    let relevant :=
      (g2nnfRelevantExSubLeftStepsOnPath path).map
        (fun step => step.eigenvariable)
    (variables ++ relevant).Nodup ∧
      AntecedentVariablesLive
        (variables ++ relevant) GammaNode := by
  induction path generalizing variables with
  | root T =>
      simpa [g2nnfRelevantExSubLeftStepsOnPath] using
        And.intro hNodup hLive
  | onePremise rule hAdmit hPrem hSC sub tail ih =>
      rcases hQuantifier with ⟨hRule, hTail⟩
      let step :=
        G2nnfProofTree.RootToNodePath.onePremise
          rule hAdmit hPrem hSC sub (.root sub)
      let subPrefix :
          G2nnfProofTree.RootToNodePath outer sub :=
        pathPrefix.trans step
      cases rule <;>
        simp only [G2nnfRuleCore.isQuantifierRule] at hRule
      next A occurrence x B t hSelected Gamma Delta =>
        have hPureSub :
            isPureVariableProofG2nnfAux outer sub subPrefix :=
          by simpa [subPrefix, step] using hPure.2
        have hLiveSub :
            AntecedentVariablesLive variables
              (((G2nnfRuleCore.allSubLeft
                A occurrence x B t hSelected Gamma Delta).premises)[0]'(by omega)).1 :=
          g2nnfQuantifierPremise_preserves_live
            (.allSubLeft A occurrence x B t hSelected Gamma Delta) hPrem hRule hLive
        simpa [g2nnfRelevantExSubLeftStepsOnPath] using
          ih subPrefix hPureSub hTail variables hNodup hLiveSub
      next A occurrence x B y hSelected Gamma Delta =>
        have hPureSub :
            isPureVariableProofG2nnfAux outer sub subPrefix :=
          by simpa [subPrefix, step] using hPure.2
        have hLiveSub :
            AntecedentVariablesLive variables
              (((G2nnfRuleCore.allSubRight
                A occurrence x B y hSelected Gamma Delta).premises)[0]'(by omega)).1 :=
          g2nnfQuantifierPremise_preserves_live
            (.allSubRight A occurrence x B y hSelected Gamma Delta) hPrem hRule hLive
        simpa [g2nnfRelevantExSubLeftStepsOnPath] using
          ih subPrefix hPureSub hTail variables hNodup hLiveSub
      next A occurrence x B y hSelected Gamma Delta =>
        classical
        by_cases hRelevant : x ∈ formulaFVN B
        · have hDec :
              Classical.propDecidable (x ∈ formulaFVN B) =
                Decidable.isTrue hRelevant :=
            Subsingleton.elim _ _
          have hPurityStep :=
            g2nnfExSubLeft_purity_step
              A B occurrence x y hSelected Gamma Delta
              hPrem hSC sub pathPrefix hPure
          have hFresh : y ∉ variables :=
            not_mem_of_g2nnfSequentVariableFree_of_live
              hPurityStep.1 hLive
          have hNodupNext :
              (variables ++ [y]).Nodup := by
            rw [List.nodup_append]
            refine ⟨hNodup, by simp, ?_⟩
            intro a ha b hb hab
            have hby : b = y := List.mem_singleton.mp hb
            subst b
            subst a
            exact hFresh ha
          have hLiveSub :
              AntecedentVariablesLive variables
                (((G2nnfRuleCore.exSubLeft
                  A occurrence x B y hSelected Gamma Delta).premises)[0]'(by omega)).1 :=
            g2nnfQuantifierPremise_preserves_live
              (.exSubLeft A occurrence x B y hSelected Gamma Delta) hPrem hRule hLive
          have hLiveNext :
              AntecedentVariablesLive (variables ++ [y])
                (((G2nnfRuleCore.exSubLeft
                  A occurrence x B y hSelected Gamma Delta).premises)[0]'(by omega)).1 :=
            antecedentVariablesLive_append_singleton
              hLiveSub
              (g2nnfExSubLeft_eigenvariable_witness
                A B occurrence x y hSelected Gamma Delta
                hSC hRelevant)
          have hPureSub :
              isPureVariableProofG2nnfAux outer sub subPrefix := by
            simpa [subPrefix, step] using hPurityStep.2
          have hTailResult :=
            ih subPrefix hPureSub hTail
              (variables ++ [y]) hNodupNext hLiveNext
          simpa [g2nnfRelevantExSubLeftStepsOnPath,
            hDec, List.append_assoc] using hTailResult
        · have hDec :
              Classical.propDecidable (x ∈ formulaFVN B) =
                Decidable.isFalse hRelevant :=
            Subsingleton.elim _ _
          have hPureSub :
              isPureVariableProofG2nnfAux outer sub subPrefix :=
            by simpa [subPrefix, step] using hPure.2
          have hLiveSub :
              AntecedentVariablesLive variables
                (((G2nnfRuleCore.exSubLeft
                  A occurrence x B y hSelected Gamma Delta).premises)[0]'(by omega)).1 :=
            g2nnfQuantifierPremise_preserves_live
              (.exSubLeft A occurrence x B y hSelected Gamma Delta) hPrem hRule hLive
          simpa [g2nnfRelevantExSubLeftStepsOnPath,
            hDec] using
            ih subPrefix hPureSub hTail
              variables hNodup hLiveSub
      next A occurrence x B t hSelected Gamma Delta =>
        have hPureSub :
            isPureVariableProofG2nnfAux outer sub subPrefix :=
          by simpa [subPrefix, step] using hPure.2
        have hLiveSub :
            AntecedentVariablesLive variables
              (((G2nnfRuleCore.exSubRight
                A occurrence x B t hSelected Gamma Delta).premises)[0]'(by omega)).1 :=
          g2nnfQuantifierPremise_preserves_live
            (.exSubRight A occurrence x B t hSelected Gamma Delta) hPrem hRule hLive
        simpa [g2nnfRelevantExSubLeftStepsOnPath] using
          ih subPrefix hPureSub hTail variables hNodup hLiveSub
  | leftPremise rule hAdmit hPrem hSC sub₁ sub₂ tail ih =>
      rcases hQuantifier with ⟨hRule, _⟩
      cases rule <;>
        simp [G2nnfRuleCore.isQuantifierRule,
          G2nnfRuleCore.premises] at hRule hPrem
  | rightPremise rule hAdmit hPrem hSC sub₁ sub₂ tail ih =>
      rcases hQuantifier with ⟨hRule, _⟩
      cases rule <;>
        simp [G2nnfRuleCore.isQuantifierRule,
          G2nnfRuleCore.premises] at hRule hPrem

/-- Relevant existential-left eigenvariables on an exact pure G2nnf
lower path are pairwise distinct in outer-to-inner order. -/
private theorem g2nnfRelevantEigenvariables_nodup
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {GammaRoot DeltaRoot GammaNode DeltaNode :
      LCS.Finset (FormulaN L)}
    (root : G2nnfProofTree hNoEq GammaRoot DeltaRoot)
    {node : G2nnfProofTree hNoEq GammaNode DeltaNode}
    (path : G2nnfProofTree.RootToNodePath root node)
    (hQuantifier : AllRulesQuantifierOnPath path)
    (hPure : IsPureVariableProofG2nnf root) :
    ((g2nnfRelevantExSubLeftStepsOnPath path).map
      (fun step => step.eigenvariable)).Nodup := by
  have hResult :=
    g2nnfRelevantEigenvariables_nodup_live
      root root (.root root) hPure path hQuantifier
      [] List.nodup_nil (by
        intro y hy
        simp at hy)
  simpa using hResult.1

/-- Equality-system accumulator proof of relevant-eigenvariable freshness.
It retains the exact equality path and excludes nonquantifier Core inferences
using the quantifier-only path evidence. -/
private theorem g2nnfEqRelevantEigenvariables_nodup_live
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {GammaRoot DeltaRoot GammaCur DeltaCur GammaNode DeltaNode :
      LCS.Finset (FormulaN L)}
    (outer : G2nnfEqProofTree hL GammaRoot DeltaRoot)
    (current : G2nnfEqProofTree hL GammaCur DeltaCur)
    (pathPrefix : G2nnfEqProofTree.RootToNodePath outer current)
    (hPure :
      isPureVariableProof_G2nnfEqAux outer current pathPrefix)
    {node : G2nnfEqProofTree hL GammaNode DeltaNode}
    (path : G2nnfEqProofTree.RootToNodePath current node)
    (hQuantifier : AllRulesQuantifierOnPath_G2nnfEq path)
    (variables : List Nat)
    (hNodup : variables.Nodup)
    (hLive :
      AntecedentVariablesLive variables GammaCur) :
    let relevant :=
      (g2nnfEqRelevantExSubLeftStepsOnPath path).map
        (fun step => step.eigenvariable)
    (variables ++ relevant).Nodup ∧
      AntecedentVariablesLive
        (variables ++ relevant) GammaNode := by
  induction path generalizing variables with
  | root T =>
      simpa [g2nnfEqRelevantExSubLeftStepsOnPath] using
        And.intro hNodup hLive
  | onePremise rule hAdmit hPrem hSC sub tail ih =>
      rcases hQuantifier with ⟨hRule, hTail⟩
      let step :=
        G2nnfEqProofTree.RootToNodePath.onePremise
          rule hAdmit hPrem hSC sub (.root sub)
      let subPrefix :
          G2nnfEqProofTree.RootToNodePath outer sub :=
        pathPrefix.trans step
      cases rule <;>
        simp only [G2nnfRuleCore.isQuantifierRule] at hRule
      next A occurrence x B t hSelected Gamma Delta =>
        have hPureSub :
            isPureVariableProof_G2nnfEqAux outer sub subPrefix :=
          by simpa [subPrefix, step] using hPure.2
        have hLiveSub :
            AntecedentVariablesLive variables
              (((G2nnfRuleCore.allSubLeft
                A occurrence x B t hSelected Gamma Delta).premises)[0]'(by omega)).1 :=
          g2nnfEqQuantifierPremise_preserves_live
            (.allSubLeft A occurrence x B t hSelected Gamma Delta) hPrem hRule hLive
        simpa [g2nnfEqRelevantExSubLeftStepsOnPath] using
          ih subPrefix hPureSub hTail variables hNodup hLiveSub
      next A occurrence x B y hSelected Gamma Delta =>
        have hPureSub :
            isPureVariableProof_G2nnfEqAux outer sub subPrefix :=
          by simpa [subPrefix, step] using hPure.2
        have hLiveSub :
            AntecedentVariablesLive variables
              (((G2nnfRuleCore.allSubRight
                A occurrence x B y hSelected Gamma Delta).premises)[0]'(by omega)).1 :=
          g2nnfEqQuantifierPremise_preserves_live
            (.allSubRight A occurrence x B y hSelected Gamma Delta) hPrem hRule hLive
        simpa [g2nnfEqRelevantExSubLeftStepsOnPath] using
          ih subPrefix hPureSub hTail variables hNodup hLiveSub
      next A occurrence x B y hSelected Gamma Delta =>
        classical
        by_cases hRelevant : x ∈ formulaFVN B
        · have hDec :
              Classical.propDecidable (x ∈ formulaFVN B) =
                Decidable.isTrue hRelevant :=
            Subsingleton.elim _ _
          have hPurityStep :=
            g2nnfEqExSubLeft_purity_step
              A B occurrence x y hSelected Gamma Delta
              hPrem hSC sub pathPrefix hPure
          have hFresh : y ∉ variables :=
            not_mem_of_g2nnfEqSequentVariableFree_of_live
              hPurityStep.1 hLive
          have hNodupNext :
              (variables ++ [y]).Nodup := by
            rw [List.nodup_append]
            refine ⟨hNodup, by simp, ?_⟩
            intro a ha b hb hab
            have hby : b = y := List.mem_singleton.mp hb
            subst b
            subst a
            exact hFresh ha
          have hLiveSub :
              AntecedentVariablesLive variables
                (((G2nnfRuleCore.exSubLeft
                  A occurrence x B y hSelected Gamma Delta).premises)[0]'(by omega)).1 :=
            g2nnfEqQuantifierPremise_preserves_live
              (.exSubLeft A occurrence x B y hSelected Gamma Delta) hPrem hRule hLive
          have hLiveNext :
              AntecedentVariablesLive (variables ++ [y])
                (((G2nnfRuleCore.exSubLeft
                  A occurrence x B y hSelected Gamma Delta).premises)[0]'(by omega)).1 :=
            antecedentVariablesLive_append_singleton
              hLiveSub
              (g2nnfEqExSubLeft_eigenvariable_witness
                A B occurrence x y hSelected Gamma Delta
                hSC hRelevant)
          have hPureSub :
              isPureVariableProof_G2nnfEqAux outer sub subPrefix := by
            simpa [subPrefix, step] using hPurityStep.2
          have hTailResult :=
            ih subPrefix hPureSub hTail
              (variables ++ [y]) hNodupNext hLiveNext
          simpa [g2nnfEqRelevantExSubLeftStepsOnPath,
            hDec, List.append_assoc] using hTailResult
        · have hDec :
              Classical.propDecidable (x ∈ formulaFVN B) =
                Decidable.isFalse hRelevant :=
            Subsingleton.elim _ _
          have hPureSub :
              isPureVariableProof_G2nnfEqAux outer sub subPrefix :=
            by simpa [subPrefix, step] using hPure.2
          have hLiveSub :
              AntecedentVariablesLive variables
                (((G2nnfRuleCore.exSubLeft
                  A occurrence x B y hSelected Gamma Delta).premises)[0]'(by omega)).1 :=
            g2nnfEqQuantifierPremise_preserves_live
              (.exSubLeft A occurrence x B y hSelected Gamma Delta) hPrem hRule hLive
          simpa [g2nnfEqRelevantExSubLeftStepsOnPath,
            hDec] using
            ih subPrefix hPureSub hTail
              variables hNodup hLiveSub
      next A occurrence x B t hSelected Gamma Delta =>
        have hPureSub :
            isPureVariableProof_G2nnfEqAux outer sub subPrefix :=
          by simpa [subPrefix, step] using hPure.2
        have hLiveSub :
            AntecedentVariablesLive variables
              (((G2nnfRuleCore.exSubRight
                A occurrence x B t hSelected Gamma Delta).premises)[0]'(by omega)).1 :=
          g2nnfEqQuantifierPremise_preserves_live
            (.exSubRight A occurrence x B t hSelected Gamma Delta) hPrem hRule hLive
        simpa [g2nnfEqRelevantExSubLeftStepsOnPath] using
          ih subPrefix hPureSub hTail variables hNodup hLiveSub
  | leftPremise rule hAdmit hPrem hSC sub₁ sub₂ tail ih =>
      rcases hQuantifier with ⟨hRule, _⟩
      cases rule <;>
        simp [G2nnfRuleCore.isQuantifierRule,
          G2nnfRuleCore.premises] at hRule hPrem
  | rightPremise rule hAdmit hPrem hSC sub₁ sub₂ tail ih =>
      rcases hQuantifier with ⟨hRule, _⟩
      cases rule <;>
        simp [G2nnfRuleCore.isQuantifierRule,
          G2nnfRuleCore.premises] at hRule hPrem

/-- Relevant existential-left eigenvariables on an exact pure G2nnf=
lower path are pairwise distinct in outer-to-inner order. -/
private theorem g2nnfEqRelevantEigenvariables_nodup
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {GammaRoot DeltaRoot GammaNode DeltaNode :
      LCS.Finset (FormulaN L)}
    (root : G2nnfEqProofTree hL GammaRoot DeltaRoot)
    {node : G2nnfEqProofTree hL GammaNode DeltaNode}
    (path : G2nnfEqProofTree.RootToNodePath root node)
    (hQuantifier :
      AllRulesQuantifierOnPath_G2nnfEq path)
    (hPure : IsPureVariableProof_G2nnfEq root) :
    ((g2nnfEqRelevantExSubLeftStepsOnPath path).map
      (fun step => step.eigenvariable)).Nodup := by
  have hResult :=
    g2nnfEqRelevantEigenvariables_nodup_live
      root root (.root root) hPure path hQuantifier
      [] List.nodup_nil (by
        intro y hy
        simp at hy)
  simpa using hResult.1

/-- A source quantifier binder together with its exact outer universal
scope.  This is occurrence-sensitive through the formula tree; rectification
is used below only to show that a binder has at most one such scope. -/
inductive QuantifierSourceScope {L : Language} :
    FormulaN L → List Nat → Nat → List Nat → Prop where
  | conjLeft
      {A B : FormulaN L} {pfx : List Nat}
      {x : Nat} {scope : List Nat}
      (inner : QuantifierSourceScope A pfx x scope) :
      QuantifierSourceScope (.conj A B) pfx x scope
  | conjRight
      {A B : FormulaN L} {pfx : List Nat}
      {x : Nat} {scope : List Nat}
      (inner : QuantifierSourceScope B pfx x scope) :
      QuantifierSourceScope (.conj A B) pfx x scope
  | disjLeft
      {A B : FormulaN L} {pfx : List Nat}
      {x : Nat} {scope : List Nat}
      (inner : QuantifierSourceScope A pfx x scope) :
      QuantifierSourceScope (.disj A B) pfx x scope
  | disjRight
      {A B : FormulaN L} {pfx : List Nat}
      {x : Nat} {scope : List Nat}
      (inner : QuantifierSourceScope B pfx x scope) :
      QuantifierSourceScope (.disj A B) pfx x scope
  | allHere
      (x : Nat) (B : FormulaN L) (pfx : List Nat) :
      QuantifierSourceScope (.all x B) pfx x pfx
  | allBody
      {x y : Nat} {B : FormulaN L} {pfx scope : List Nat}
      (inner :
        QuantifierSourceScope B (pfx ++ [x]) y scope) :
      QuantifierSourceScope (.all x B) pfx y scope
  | exHere
      (x : Nat) (B : FormulaN L) (pfx : List Nat) :
      QuantifierSourceScope (.ex x B) pfx x pfx
  | exBody
      {x y : Nat} {B : FormulaN L} {pfx scope : List Nat}
      (inner :
        QuantifierSourceScope B pfx y scope) :
      QuantifierSourceScope (.ex x B) pfx y scope

/-- Any binder named by a source-scope derivation really occurs bound in
the formula indexing that derivation. -/
private theorem quantifierSourceScope_binder_mem
    {L : Language} {A : FormulaN L} {pfx : List Nat}
    {x : Nat} {scope : List Nat}
    (hScope : QuantifierSourceScope A pfx x scope) :
    x ∈ formulaBVN A := by
  induction hScope with
  | conjLeft _ ih =>
      exact Or.inl ih
  | conjRight _ ih =>
      exact Or.inr ih
  | disjLeft _ ih =>
      exact Or.inl ih
  | disjRight _ ih =>
      exact Or.inr ih
  | allHere =>
      exact Or.inr rfl
  | allBody _ ih =>
      exact Or.inl ih
  | exHere =>
      exact Or.inr rfl
  | exBody _ ih =>
      exact Or.inl ih

/-- Distinct quantifier bindings make the universal scope determined by
the binder name.  This is where rectification prevents two syntactically
different source occurrences from sharing a lookup key. -/
theorem quantifierSourceScope_unique
    {L : Language} {A : FormulaN L} {pfx : List Nat}
    {x : Nat} {scope₁ scope₂ : List Nat}
    (hDistinct : distinctQuantifierBindings A)
    (h₁ : QuantifierSourceScope A pfx x scope₁)
    (h₂ : QuantifierSourceScope A pfx x scope₂) :
    scope₁ = scope₂ := by
  induction h₁ generalizing scope₂ with
  | conjLeft hLeft ih =>
      cases h₂ with
      | conjLeft hOther =>
          exact ih hDistinct.1 hOther
      | conjRight hOther =>
          exact False.elim
            (hDistinct.2.2 _
              ⟨quantifierSourceScope_binder_mem hLeft,
                quantifierSourceScope_binder_mem hOther⟩)
  | conjRight hRight ih =>
      cases h₂ with
      | conjLeft hOther =>
          exact False.elim
            (hDistinct.2.2 _
              ⟨quantifierSourceScope_binder_mem hOther,
                quantifierSourceScope_binder_mem hRight⟩)
      | conjRight hOther =>
          exact ih hDistinct.2.1 hOther
  | disjLeft hLeft ih =>
      cases h₂ with
      | disjLeft hOther =>
          exact ih hDistinct.1 hOther
      | disjRight hOther =>
          exact False.elim
            (hDistinct.2.2 _
              ⟨quantifierSourceScope_binder_mem hLeft,
                quantifierSourceScope_binder_mem hOther⟩)
  | disjRight hRight ih =>
      cases h₂ with
      | disjLeft hOther =>
          exact False.elim
            (hDistinct.2.2 _
              ⟨quantifierSourceScope_binder_mem hOther,
                quantifierSourceScope_binder_mem hRight⟩)
      | disjRight hOther =>
          exact ih hDistinct.2.1 hOther
  | allHere x B pfx =>
      cases h₂ with
      | allHere =>
          rfl
      | allBody hOther =>
          exact False.elim
            (hDistinct.2
              (quantifierSourceScope_binder_mem hOther))
  | allBody hInner ih =>
      cases h₂ with
      | allHere =>
          exact False.elim
            (hDistinct.2
              (quantifierSourceScope_binder_mem hInner))
      | allBody hOther =>
          exact ih hDistinct.1 hOther
  | exHere x B pfx =>
      cases h₂ with
      | exHere =>
          rfl
      | exBody hOther =>
          exact False.elim
            (hDistinct.2
              (quantifierSourceScope_binder_mem hOther))
  | exBody hInner ih =>
      cases h₂ with
      | exHere =>
          exact False.elim
            (hDistinct.2
              (quantifierSourceScope_binder_mem hInner))
      | exBody hOther =>
          exact ih hDistinct.1 hOther

/-- An exact allocation descriptor induces the corresponding
source-quantifier scope derivation. -/
private theorem quantifierSourceScope_of_descriptor
    {L : Language} {A : FormulaN L} {pfx scope : List Nat}
    {x : Nat} {B : FormulaN L}
    (hDescriptor :
      (FormulaN.ex x B, scope) ∈
        existentialDescriptorsAux A pfx) :
    QuantifierSourceScope A pfx x scope := by
  induction A generalizing pfx with
  | predN _ _ =>
      simp [existentialDescriptorsAux, universalScopeAux] at hDescriptor
  | eq_ _ _ _ =>
      simp [existentialDescriptorsAux, universalScopeAux] at hDescriptor
  | neg _ _ =>
      simp [existentialDescriptorsAux, universalScopeAux] at hDescriptor
  | conj C D ihC ihD =>
      simp [existentialDescriptorsAux, universalScopeAux,
        List.filterMap_append] at hDescriptor
      rcases hDescriptor with hDescriptor | hDescriptor
      · exact .conjLeft (ihC (by simpa [existentialDescriptorsAux] using hDescriptor))
      · exact .conjRight (ihD (by simpa [existentialDescriptorsAux] using hDescriptor))
  | disj C D ihC ihD =>
      simp [existentialDescriptorsAux, universalScopeAux,
        List.filterMap_append] at hDescriptor
      rcases hDescriptor with hDescriptor | hDescriptor
      · exact .disjLeft (ihC (by simpa [existentialDescriptorsAux] using hDescriptor))
      · exact .disjRight (ihD (by simpa [existentialDescriptorsAux] using hDescriptor))
  | impl _ _ _ _ =>
      simp [existentialDescriptorsAux, universalScopeAux] at hDescriptor
  | all y C ih =>
      exact .allBody (ih hDescriptor)
  | ex y C ih =>
      change (FormulaN.ex x B, scope) ∈
        (FormulaN.ex y C, pfx) :: existentialDescriptorsAux C pfx at hDescriptor
      rcases List.mem_cons.mp hDescriptor with hHere | hDescriptor
      · injection hHere with hFormula hScope
        cases hFormula
        cases hScope
        exact .exHere _ _ _
      · exact .exBody (ih hDescriptor)

/-- The exact allocation index carries its source scope independently of
the later proof path. -/
theorem skolemAllocation_sourceScope
    {L : Language} (spec : SkolemSpec L)
    (i : Fin spec.n) {x : Nat} {B : FormulaN L}
    {scope : List Nat}
    (hAllocation :
      spec.allocation i = (FormulaN.ex x B, scope)) :
    QuantifierSourceScope spec.source [] x scope := by
  have hMember : spec.allocation i ∈ spec.allocations :=
    List.get_mem spec.allocations i
  rw [SkolemSpec.allocations, existentialDescriptors] at hMember
  rw [hAllocation] at hMember
  exact quantifierSourceScope_of_descriptor hMember

/-- Every variable in `scope` has an explicit closed choice in the map.
This is the certificate that rules out the seed branch when an exact
Skolem allocation is closed. -/
def ClosedEigenvarMap.Covers
    {L : Language} (eigenMap : ClosedEigenvarMap L)
    (scope : List Nat) : Prop :=
  ∀ x, x ∈ scope →
    ∃ choice, eigenMap.lookup x = some choice

private theorem ClosedEigenvarMap.covers_nil
    {L : Language} (eigenMap : ClosedEigenvarMap L) :
    eigenMap.Covers [] := by
  intro x hx
  cases hx

private theorem ClosedEigenvarMap.covers_insert
    {L : Language} (eigenMap : ClosedEigenvarMap L)
    (x : Nat) (choice : ClosedTerm L) {scope : List Nat}
    (hCovers : eigenMap.Covers scope) :
    (eigenMap.insert x choice).Covers scope := by
  intro y hy
  by_cases hyx : y = x
  · subst y
    exact ⟨choice, ClosedEigenvarMap.lookup_insert_self
      eigenMap x choice⟩
  · obtain ⟨priorChoice, hPriorChoice⟩ :=
      hCovers y hy
    exact
      ⟨priorChoice, by
        rw [ClosedEigenvarMap.lookup_insert_of_ne
          eigenMap x y choice hyx]
        exact hPriorChoice⟩

private theorem ClosedEigenvarMap.covers_append_insert
    {L : Language} (eigenMap : ClosedEigenvarMap L)
    (x : Nat) (choice : ClosedTerm L) {scope : List Nat}
    (hCovers : eigenMap.Covers scope) :
    (eigenMap.insert x choice).Covers (scope ++ [x]) := by
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact eigenMap.covers_insert x choice hCovers y hy
  · have hyx : y = x := List.mem_singleton.mp hy
    subst y
    exact ⟨choice, ClosedEigenvarMap.lookup_insert_self
      eigenMap x choice⟩

/-- Exact source scopes of the quantifiers currently exposed through
only conjunction/disjunction nodes. -/
private def ClosedFormulaFrontierScopes
    {L : Language} (spec : SkolemSpec L) :
    FormulaN L → List Nat → Prop
  | .conj A B, scope =>
      ClosedFormulaFrontierScopes spec A scope ∧
        ClosedFormulaFrontierScopes spec B scope
  | .disj A B, scope =>
      ClosedFormulaFrontierScopes spec A scope ∧
        ClosedFormulaFrontierScopes spec B scope
  | .all x _, scope =>
      QuantifierSourceScope spec.source [] x scope
  | .ex x _, scope =>
      QuantifierSourceScope spec.source [] x scope
  | _, _ => True

/-- Every quantifier node retains its exact source-scope relationship to
the quantifiers exposed immediately inside its body. -/
private def ClosedFormulaScopeAligned
    {L : Language} (spec : SkolemSpec L) : FormulaN L → Prop
  | .conj A B =>
      ClosedFormulaScopeAligned spec A ∧
        ClosedFormulaScopeAligned spec B
  | .disj A B =>
      ClosedFormulaScopeAligned spec A ∧
        ClosedFormulaScopeAligned spec B
  | .all x B =>
      ∃ scope,
        QuantifierSourceScope spec.source [] x scope ∧
          ClosedFormulaFrontierScopes spec B (scope ++ [x]) ∧
          ClosedFormulaScopeAligned spec B
  | .ex x B =>
      ∃ scope,
        QuantifierSourceScope spec.source [] x scope ∧
          ClosedFormulaFrontierScopes spec B scope ∧
          ClosedFormulaScopeAligned spec B
  | _ => True

/-- Every currently exposed quantifier has all of its already-eliminated
source universal pfx explicitly represented in the provenance map. -/
private def ClosedFormulaFrontierReady
    {L : Language} (spec : SkolemSpec L)
    (eigenMap : ClosedEigenvarMap spec.language) :
    FormulaN L → Prop
  | .conj A B =>
      ClosedFormulaFrontierReady spec eigenMap A ∧
        ClosedFormulaFrontierReady spec eigenMap B
  | .disj A B =>
      ClosedFormulaFrontierReady spec eigenMap A ∧
        ClosedFormulaFrontierReady spec eigenMap B
  | .all x _ =>
      ∃ scope,
        QuantifierSourceScope spec.source [] x scope ∧
          eigenMap.Covers scope
  | .ex x _ =>
      ∃ scope,
        QuantifierSourceScope spec.source [] x scope ∧
          eigenMap.Covers scope
  | _ => True

private theorem closedFormulaFrontierScopes_of_local
    {L : Language} (spec : SkolemSpec L)
    (A : FormulaN L) (pfx : List Nat)
    (hEmbed :
      ∀ {x scope},
        QuantifierSourceScope A pfx x scope →
          QuantifierSourceScope spec.source [] x scope) :
    ClosedFormulaFrontierScopes spec A pfx := by
  induction A generalizing pfx with
  | conj B C ihB ihC =>
      exact
        ⟨ihB pfx (fun h => hEmbed (.conjLeft h)),
          ihC pfx (fun h => hEmbed (.conjRight h))⟩
  | disj B C ihB ihC =>
      exact
        ⟨ihB pfx (fun h => hEmbed (.disjLeft h)),
          ihC pfx (fun h => hEmbed (.disjRight h))⟩
  | all x B =>
      exact hEmbed (.allHere x B pfx)
  | ex x B =>
      exact hEmbed (.exHere x B pfx)
  | predN _ _ =>
      trivial
  | eq_ _ _ _ =>
      trivial
  | neg _ _ =>
      trivial
  | impl _ _ _ _ =>
      trivial

private theorem closedFormulaScopeAligned_of_local
    {L : Language} (spec : SkolemSpec L)
    (A : FormulaN L) (pfx : List Nat)
    (hEmbed :
      ∀ {x scope},
        QuantifierSourceScope A pfx x scope →
          QuantifierSourceScope spec.source [] x scope) :
    ClosedFormulaScopeAligned spec A := by
  induction A generalizing pfx with
  | conj B C ihB ihC =>
      exact
        ⟨ihB pfx (fun h => hEmbed (.conjLeft h)),
          ihC pfx (fun h => hEmbed (.conjRight h))⟩
  | disj B C ihB ihC =>
      exact
        ⟨ihB pfx (fun h => hEmbed (.disjLeft h)),
          ihC pfx (fun h => hEmbed (.disjRight h))⟩
  | all x B ih =>
      let hBodyEmbed :
          ∀ {y scope},
            QuantifierSourceScope B (pfx ++ [x]) y scope →
              QuantifierSourceScope spec.source [] y scope :=
        fun h => hEmbed (.allBody h)
      exact
        ⟨pfx, hEmbed (.allHere x B pfx),
          closedFormulaFrontierScopes_of_local
            spec B (pfx ++ [x]) hBodyEmbed,
          ih (pfx ++ [x]) hBodyEmbed⟩
  | ex x B ih =>
      let hBodyEmbed :
          ∀ {y scope},
            QuantifierSourceScope B pfx y scope →
              QuantifierSourceScope spec.source [] y scope :=
        fun h => hEmbed (.exBody h)
      exact
        ⟨pfx, hEmbed (.exHere x B pfx),
          closedFormulaFrontierScopes_of_local
            spec B pfx hBodyEmbed,
          ih pfx hBodyEmbed⟩
  | predN _ _ =>
      trivial
  | eq_ _ _ _ =>
      trivial
  | neg _ _ =>
      trivial
  | impl _ _ _ _ =>
      trivial

private theorem closedFormulaScopeAligned_source
    {L : Language} (spec : SkolemSpec L) :
    ClosedFormulaScopeAligned spec spec.source :=
  closedFormulaScopeAligned_of_local
    spec spec.source [] (fun h => h)

private theorem closedFormulaFrontierReady_source
    {L : Language} (spec : SkolemSpec L) :
    ClosedFormulaFrontierReady spec
      (ClosedEigenvarMap.empty : ClosedEigenvarMap spec.language)
      spec.source := by
  have hScopes :=
    closedFormulaFrontierScopes_of_local
      spec spec.source [] (fun h => h)
  revert hScopes
  generalize spec.source = A
  intro hScopes
  induction A with
  | conj A B ihA ihB =>
      exact
        ⟨ihA hScopes.1, ihB hScopes.2⟩
  | disj A B ihA ihB =>
      exact
        ⟨ihA hScopes.1, ihB hScopes.2⟩
  | all x B =>
      exact ⟨[], hScopes,
        ClosedEigenvarMap.covers_nil
          (ClosedEigenvarMap.empty :
            ClosedEigenvarMap spec.language)⟩
  | ex x B =>
      exact ⟨[], hScopes,
        ClosedEigenvarMap.covers_nil
          (ClosedEigenvarMap.empty :
            ClosedEigenvarMap spec.language)⟩
  | predN _ _ =>
      trivial
  | eq_ _ _ _ =>
      trivial
  | neg _ _ =>
      trivial
  | impl _ _ _ _ =>
      trivial

private theorem closedFormulaFrontierScopes_subst
    {L : Language} (spec : SkolemSpec L)
    (A : FormulaN L) (t : Term L) (x : Nat)
    (scope : List Nat)
    (hScopes : ClosedFormulaFrontierScopes spec A scope) :
    ClosedFormulaFrontierScopes spec
      (formulaSubstN A t x) scope := by
  induction A with
  | conj B C ihB ihC =>
      exact ⟨ihB hScopes.1, ihC hScopes.2⟩
  | disj B C ihB ihC =>
      exact ⟨ihB hScopes.1, ihC hScopes.2⟩
  | all y B =>
      by_cases hxy : x = y <;>
        simpa [formulaSubstN, hxy, ClosedFormulaFrontierScopes] using hScopes
  | ex y B =>
      by_cases hxy : x = y <;>
        simpa [formulaSubstN, hxy, ClosedFormulaFrontierScopes] using hScopes
  | predN _ _ =>
      trivial
  | eq_ _ _ _ =>
      trivial
  | neg _ _ =>
      trivial
  | impl _ _ _ _ =>
      trivial

private theorem closedFormulaScopeAligned_subst
    {L : Language} (spec : SkolemSpec L)
    (A : FormulaN L) (t : Term L) (x : Nat)
    (hAligned : ClosedFormulaScopeAligned spec A) :
    ClosedFormulaScopeAligned spec (formulaSubstN A t x) := by
  induction A with
  | conj B C ihB ihC =>
      exact ⟨ihB hAligned.1, ihC hAligned.2⟩
  | disj B C ihB ihC =>
      exact ⟨ihB hAligned.1, ihC hAligned.2⟩
  | all y B ih =>
      by_cases hxy : x = y
      · subst y
        simpa only [formulaSubstN, bne_self_eq_false,
          Bool.false_eq_true, if_false] using hAligned
      · simp only [formulaSubstN, bne_iff_ne.mpr hxy, if_true]
        rcases hAligned with
          ⟨scope, hSource, hScopes, hBody⟩
        refine ⟨scope, hSource, ?_, ?_⟩
        · simpa only [formulaSubstN,
            bne_iff_ne.mpr hxy, if_true] using
            closedFormulaFrontierScopes_subst
              spec B t x (scope ++ [y]) hScopes
        · simpa only [formulaSubstN,
            bne_iff_ne.mpr hxy, if_true] using ih hBody
  | ex y B ih =>
      by_cases hxy : x = y
      · subst y
        simpa only [formulaSubstN, bne_self_eq_false,
          Bool.false_eq_true, if_false] using hAligned
      · simp only [formulaSubstN, bne_iff_ne.mpr hxy, if_true]
        rcases hAligned with
          ⟨scope, hSource, hScopes, hBody⟩
        refine ⟨scope, hSource, ?_, ?_⟩
        · simpa only [formulaSubstN,
            bne_iff_ne.mpr hxy, if_true] using
            closedFormulaFrontierScopes_subst
              spec B t x scope hScopes
        · simpa only [formulaSubstN,
            bne_iff_ne.mpr hxy, if_true] using ih hBody
  | predN _ _ =>
      trivial
  | eq_ _ _ _ =>
      trivial
  | neg B ih =>
      trivial
  | impl B C ihB ihC =>
      trivial

private theorem closedFormulaScopeAligned_replace
    {L : Language} {spec : SkolemSpec L}
    {A : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A)
    (replacement : FormulaN L)
    (hAligned : ClosedFormulaScopeAligned spec A)
    (hReplacement :
      ClosedFormulaScopeAligned spec replacement) :
    ClosedFormulaScopeAligned spec
      (occurrence.replace replacement) := by
  induction occurrence with
  | all _ _ =>
      exact hReplacement
  | ex _ _ =>
      exact hReplacement
  | conjLeft inner C ih =>
      exact ⟨ih hAligned.1, hAligned.2⟩
  | conjRight C inner ih =>
      exact ⟨hAligned.1, ih hAligned.2⟩
  | disjLeft inner C ih =>
      exact ⟨ih hAligned.1, hAligned.2⟩
  | disjRight C inner ih =>
      exact ⟨hAligned.1, ih hAligned.2⟩

private theorem closedFormulaFrontierReady_of_scopes
    {L : Language} (spec : SkolemSpec L)
    (eigenMap : ClosedEigenvarMap spec.language)
    (A : FormulaN L) (scope : List Nat)
    (hScopes : ClosedFormulaFrontierScopes spec A scope)
    (hCovers : eigenMap.Covers scope) :
    ClosedFormulaFrontierReady spec eigenMap A := by
  induction A with
  | conj B C ihB ihC =>
      exact ⟨ihB hScopes.1,
        ihC hScopes.2⟩
  | disj B C ihB ihC =>
      exact ⟨ihB hScopes.1,
        ihC hScopes.2⟩
  | all x B =>
      exact ⟨scope, hScopes, hCovers⟩
  | ex x B =>
      exact ⟨scope, hScopes, hCovers⟩
  | predN _ _ =>
      trivial
  | eq_ _ _ _ =>
      trivial
  | neg _ _ =>
      trivial
  | impl _ _ _ _ =>
      trivial

private theorem closedFormulaFrontierReady_insert
    {L : Language} (spec : SkolemSpec L)
    (eigenMap : ClosedEigenvarMap spec.language)
    (x : Nat) (choice : ClosedTerm spec.language)
    (A : FormulaN L)
    (hReady :
      ClosedFormulaFrontierReady spec eigenMap A) :
    ClosedFormulaFrontierReady spec
      (eigenMap.insert x choice) A := by
  induction A with
  | conj B C ihB ihC =>
      exact ⟨ihB hReady.1, ihC hReady.2⟩
  | disj B C ihB ihC =>
      exact ⟨ihB hReady.1, ihC hReady.2⟩
  | all y B =>
      rcases hReady with ⟨scope, hSource, hCovers⟩
      exact
        ⟨scope, hSource,
          eigenMap.covers_insert x choice hCovers⟩
  | ex y B =>
      rcases hReady with ⟨scope, hSource, hCovers⟩
      exact
        ⟨scope, hSource,
          eigenMap.covers_insert x choice hCovers⟩
  | predN _ _ =>
      trivial
  | eq_ _ _ _ =>
      trivial
  | neg _ _ =>
      trivial
  | impl _ _ _ _ =>
      trivial

private theorem closedFormulaFrontierReady_replace
    {L : Language} {spec : SkolemSpec L}
    {eigenMap : ClosedEigenvarMap spec.language}
    {A : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A)
    (replacement : FormulaN L)
    (hReady : ClosedFormulaFrontierReady spec eigenMap A)
    (hReplacement :
      ClosedFormulaFrontierReady spec eigenMap replacement) :
    ClosedFormulaFrontierReady spec eigenMap
      (occurrence.replace replacement) := by
  induction occurrence with
  | all _ _ =>
      exact hReplacement
  | ex _ _ =>
      exact hReplacement
  | conjLeft inner C ih =>
      exact ⟨ih hReady.1, hReady.2⟩
  | conjRight C inner ih =>
      exact ⟨hReady.1, ih hReady.2⟩
  | disjLeft inner C ih =>
      exact ⟨ih hReady.1, hReady.2⟩
  | disjRight C inner ih =>
      exact ⟨hReady.1, ih hReady.2⟩

private theorem closedFormulaScopeAligned_selected_all
    {L : Language} {spec : SkolemSpec L}
    {A B : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A)
    (x : Nat)
    (hSelected :
      occurrence.selected = FormulaN.all x B)
    (hAligned : ClosedFormulaScopeAligned spec A) :
    ∃ scope,
      QuantifierSourceScope spec.source [] x scope ∧
        ClosedFormulaFrontierScopes spec B (scope ++ [x]) ∧
        ClosedFormulaScopeAligned spec B := by
  induction occurrence with
  | all y C =>
      cases hSelected
      exact hAligned
  | ex y C =>
      cases hSelected
  | conjLeft inner C ih =>
      exact ih hSelected hAligned.1
  | conjRight C inner ih =>
      exact ih hSelected hAligned.2
  | disjLeft inner C ih =>
      exact ih hSelected hAligned.1
  | disjRight C inner ih =>
      exact ih hSelected hAligned.2

private theorem closedFormulaScopeAligned_selected_ex
    {L : Language} {spec : SkolemSpec L}
    {A B : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A)
    (x : Nat)
    (hSelected :
      occurrence.selected = FormulaN.ex x B)
    (hAligned : ClosedFormulaScopeAligned spec A) :
    ∃ scope,
      QuantifierSourceScope spec.source [] x scope ∧
        ClosedFormulaFrontierScopes spec B scope ∧
        ClosedFormulaScopeAligned spec B := by
  induction occurrence with
  | all y C =>
      cases hSelected
  | ex y C =>
      cases hSelected
      exact hAligned
  | conjLeft inner C ih =>
      exact ih hSelected hAligned.1
  | conjRight C inner ih =>
      exact ih hSelected hAligned.2
  | disjLeft inner C ih =>
      exact ih hSelected hAligned.1
  | disjRight C inner ih =>
      exact ih hSelected hAligned.2

private theorem closedFormulaFrontierReady_selected_all
    {L : Language} {spec : SkolemSpec L}
    {eigenMap : ClosedEigenvarMap spec.language}
    {A B : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A)
    (x : Nat)
    (hSelected :
      occurrence.selected = FormulaN.all x B)
    (hReady : ClosedFormulaFrontierReady spec eigenMap A) :
    ∃ scope,
      QuantifierSourceScope spec.source [] x scope ∧
        eigenMap.Covers scope := by
  induction occurrence with
  | all y C =>
      cases hSelected
      exact hReady
  | ex y C =>
      cases hSelected
  | conjLeft inner C ih =>
      exact ih hSelected hReady.1
  | conjRight C inner ih =>
      exact ih hSelected hReady.2
  | disjLeft inner C ih =>
      exact ih hSelected hReady.1
  | disjRight C inner ih =>
      exact ih hSelected hReady.2

theorem closedFormulaFrontierReady_selected_ex
    {L : Language} {spec : SkolemSpec L}
    {eigenMap : ClosedEigenvarMap spec.language}
    {A B : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A)
    (x : Nat)
    (hSelected :
      occurrence.selected = FormulaN.ex x B)
    (hReady : ClosedFormulaFrontierReady spec eigenMap A) :
    ∃ scope,
      QuantifierSourceScope spec.source [] x scope ∧
        eigenMap.Covers scope := by
  induction occurrence with
  | all y C =>
      cases hSelected
  | ex y C =>
      cases hSelected
      exact hReady
  | conjLeft inner C ih =>
      exact ih hSelected hReady.1
  | conjRight C inner ih =>
      exact ih hSelected hReady.2
  | disjLeft inner C ih =>
      exact ih hSelected hReady.1
  | disjRight C inner ih =>
      exact ih hSelected hReady.2

private theorem closedFormulaAllSubLeft_invariants
    {L : Language} {spec : SkolemSpec L}
    {A B : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A)
    (x : Nat) (t : Term L)
    (hSelected :
      occurrence.selected = FormulaN.all x B)
    (eigenMap : ClosedEigenvarMap spec.language)
    (choice : ClosedTerm spec.language)
    (hAligned : ClosedFormulaScopeAligned spec A)
    (hReady : ClosedFormulaFrontierReady spec eigenMap A) :
    ClosedFormulaScopeAligned spec
        (occurrence.replace (formulaSubstN B t x)) ∧
      ClosedFormulaFrontierReady spec
        (eigenMap.insert x choice)
        (occurrence.replace (formulaSubstN B t x)) := by
  obtain ⟨alignedScope, hAlignedSource,
      hBodyScopes, hBodyAligned⟩ :=
    closedFormulaScopeAligned_selected_all
      occurrence x hSelected hAligned
  obtain ⟨readyScope, hReadySource, hReadyCovers⟩ :=
    closedFormulaFrontierReady_selected_all
      occurrence x hSelected hReady
  have hScopeEq : readyScope = alignedScope :=
    quantifierSourceScope_unique spec.hRect.2
      hReadySource hAlignedSource
  subst readyScope
  have hReplacementAligned :
      ClosedFormulaScopeAligned spec
        (formulaSubstN B t x) :=
    closedFormulaScopeAligned_subst
      spec B t x hBodyAligned
  have hReplacementScopes :
      ClosedFormulaFrontierScopes spec
        (formulaSubstN B t x) (alignedScope ++ [x]) :=
    closedFormulaFrontierScopes_subst
      spec B t x (alignedScope ++ [x]) hBodyScopes
  have hReplacementReady :
      ClosedFormulaFrontierReady spec
        (eigenMap.insert x choice)
        (formulaSubstN B t x) :=
    closedFormulaFrontierReady_of_scopes
      spec (eigenMap.insert x choice)
      (formulaSubstN B t x) (alignedScope ++ [x])
      hReplacementScopes
      (eigenMap.covers_append_insert x choice hReadyCovers)
  exact
    ⟨closedFormulaScopeAligned_replace
        occurrence (formulaSubstN B t x)
        hAligned hReplacementAligned,
      closedFormulaFrontierReady_replace
        occurrence (formulaSubstN B t x)
        (closedFormulaFrontierReady_insert
          spec eigenMap x choice A hReady)
        hReplacementReady⟩

theorem closedFormulaExSubLeft_invariants
    {L : Language} {spec : SkolemSpec L}
    {A B : FormulaN L}
    (occurrence : MaxQuantifierOccurrence A)
    (x : Nat) (t : Term L)
    (hSelected :
      occurrence.selected = FormulaN.ex x B)
    (eigenMap : ClosedEigenvarMap spec.language)
    (hAligned : ClosedFormulaScopeAligned spec A)
    (hReady : ClosedFormulaFrontierReady spec eigenMap A) :
    ClosedFormulaScopeAligned spec
        (occurrence.replace (formulaSubstN B t x)) ∧
      ClosedFormulaFrontierReady spec eigenMap
        (occurrence.replace (formulaSubstN B t x)) := by
  obtain ⟨alignedScope, hAlignedSource,
      hBodyScopes, hBodyAligned⟩ :=
    closedFormulaScopeAligned_selected_ex
      occurrence x hSelected hAligned
  obtain ⟨readyScope, hReadySource, hReadyCovers⟩ :=
    closedFormulaFrontierReady_selected_ex
      occurrence x hSelected hReady
  have hScopeEq : readyScope = alignedScope :=
    quantifierSourceScope_unique spec.hRect.2
      hReadySource hAlignedSource
  subst readyScope
  have hReplacementAligned :
      ClosedFormulaScopeAligned spec
        (formulaSubstN B t x) :=
    closedFormulaScopeAligned_subst
      spec B t x hBodyAligned
  have hReplacementScopes :
      ClosedFormulaFrontierScopes spec
        (formulaSubstN B t x) alignedScope :=
    closedFormulaFrontierScopes_subst
      spec B t x alignedScope hBodyScopes
  have hReplacementReady :
      ClosedFormulaFrontierReady spec eigenMap
        (formulaSubstN B t x) :=
    closedFormulaFrontierReady_of_scopes
      spec eigenMap (formulaSubstN B t x) alignedScope
      hReplacementScopes hReadyCovers
  exact
    ⟨closedFormulaScopeAligned_replace
        occurrence (formulaSubstN B t x)
        hAligned hReplacementAligned,
      closedFormulaFrontierReady_replace
        occurrence (formulaSubstN B t x)
        hReady hReplacementReady⟩

/-- One proof-relevant principal event in an antecedent formula history.
Both formula endpoints are stored as data.  Universal events freeze the
closed choice and the exact pfx map used to close it.  Relevant
existential events carry explicit coverage of the allocation scope, so
their range cannot use the seed fallback. -/
inductive ClosedFormulaProvenanceEvent
    {L : Language} (spec : SkolemSpec L)
    (seed : ClosedTerm spec.language) : Type where
  | allSubLeft
      (A B : FormulaN L)
      (occurrence : MaxQuantifierOccurrence A)
      (x : Nat) (t : Term L)
      (hSelected :
        occurrence.selected = FormulaN.all x B)
      (prefixMap : ClosedEigenvarMap spec.language)
      (choice : ClosedTerm spec.language)
      (hChoice :
        choice.1 =
          closeSkolemTermWithSeed seed prefixMap
            (liftEigenvarBaseTerm spec t)) :
      ClosedFormulaProvenanceEvent spec seed
  | exSubLeftRelevant
      (A B : FormulaN L)
      (occurrence : MaxQuantifierOccurrence A)
      (x y : Nat)
      (hSelected :
        occurrence.selected = FormulaN.ex x B)
      (hRelevant : x ∈ formulaFVN B)
      (index : Fin spec.n)
      (choiceMap : ClosedEigenvarMap spec.language)
      (hScopeCovered :
        choiceMap.Covers (spec.skolemScope index))
      (closedRange : ClosedTerm spec.language)
      (hRange :
        closedRange.1 =
          closeSkolemTermWithSeed seed choiceMap
            (exactSkolemTerm spec index)) :
      ClosedFormulaProvenanceEvent spec seed
  | exSubLeftVacuous
      (A B : FormulaN L)
      (occurrence : MaxQuantifierOccurrence A)
      (x y : Nat)
      (hSelected :
        occurrence.selected = FormulaN.ex x B)
      (hVacuous : x ∉ formulaFVN B) :
      ClosedFormulaProvenanceEvent spec seed

/-- Indexed replay of a single formula lineage from the exact source.
The formula, universal-choice map, and event list are all result indices:
an arbitrary list/map cannot be attached to an unrelated current formula. -/
inductive ClosedFormulaProvenanceReplay
    {L : Language} (spec : SkolemSpec L)
    (seed : ClosedTerm spec.language) :
    FormulaN L →
    ClosedEigenvarMap spec.language →
    List (ClosedFormulaProvenanceEvent spec seed) → Type where
  | source :
      ClosedFormulaProvenanceReplay spec seed spec.source
        ClosedEigenvarMap.empty []
  | allSubLeft
      {A B : FormulaN L}
      {universalMap : ClosedEigenvarMap spec.language}
      {events : List (ClosedFormulaProvenanceEvent spec seed)}
      (prior :
        ClosedFormulaProvenanceReplay
          spec seed A universalMap events)
      (occurrence : MaxQuantifierOccurrence A)
      (x : Nat) (t : Term L)
      (hSelected :
        occurrence.selected = FormulaN.all x B)
      (prefixMap : ClosedEigenvarMap spec.language) :
      ClosedFormulaProvenanceReplay spec seed
        (occurrence.replace (formulaSubstN B t x))
        (universalMap.insert x
          ⟨closeSkolemTermWithSeed seed prefixMap
              (liftEigenvarBaseTerm spec t),
            closeSkolemTermWithSeed_isClosed seed prefixMap
              (liftEigenvarBaseTerm spec t)⟩)
        (events ++
          [.allSubLeft A B occurrence x t hSelected prefixMap
            ⟨closeSkolemTermWithSeed seed prefixMap
                (liftEigenvarBaseTerm spec t),
              closeSkolemTermWithSeed_isClosed seed prefixMap
                (liftEigenvarBaseTerm spec t)⟩ rfl])
  | exSubLeftRelevant
      {A B : FormulaN L}
      {universalMap : ClosedEigenvarMap spec.language}
      {events : List (ClosedFormulaProvenanceEvent spec seed)}
      (prior :
        ClosedFormulaProvenanceReplay
          spec seed A universalMap events)
      (occurrence : MaxQuantifierOccurrence A)
      (x y : Nat)
      (hSelected :
        occurrence.selected = FormulaN.ex x B)
      (hRelevant : x ∈ formulaFVN B)
      (index : Fin spec.n)
      (hScopeCovered :
        universalMap.Covers (spec.skolemScope index))
      (closedRange : ClosedTerm spec.language)
      (hRange :
        closedRange.1 =
          closeSkolemTermWithSeed seed universalMap
            (exactSkolemTerm spec index)) :
      ClosedFormulaProvenanceReplay spec seed
        (occurrence.replace
          (formulaSubstN B (.var y) x))
        universalMap
        (events ++
          [.exSubLeftRelevant A B occurrence x y hSelected
            hRelevant index universalMap hScopeCovered
            closedRange hRange])
  | exSubLeftVacuous
      {A B : FormulaN L}
      {universalMap : ClosedEigenvarMap spec.language}
      {events : List (ClosedFormulaProvenanceEvent spec seed)}
      (prior :
        ClosedFormulaProvenanceReplay
          spec seed A universalMap events)
      (occurrence : MaxQuantifierOccurrence A)
      (x y : Nat)
      (hSelected :
        occurrence.selected = FormulaN.ex x B)
      (hVacuous : x ∉ formulaFVN B) :
      ClosedFormulaProvenanceReplay spec seed
        (occurrence.replace
          (formulaSubstN B (.var y) x))
        universalMap
        (events ++
          [.exSubLeftVacuous A B occurrence x y hSelected
            hVacuous])

/-- A construction-enforced source-to-current formula history. -/
structure ClosedFormulaProvenance
    {L : Language} (spec : SkolemSpec L)
    (seed : ClosedTerm spec.language)
    (current : FormulaN L) : Type where
  events : List (ClosedFormulaProvenanceEvent spec seed)
  universalMap : ClosedEigenvarMap spec.language
  replay :
    ClosedFormulaProvenanceReplay
      spec seed current universalMap events
  scopeAligned :
    ClosedFormulaScopeAligned spec current
  frontierReady :
    ClosedFormulaFrontierReady spec universalMap current

def ClosedFormulaProvenance.source
    {L : Language} (spec : SkolemSpec L)
    (seed : ClosedTerm spec.language) :
    ClosedFormulaProvenance spec seed spec.source :=
  ⟨[], ClosedEigenvarMap.empty, .source,
    closedFormulaScopeAligned_source spec,
    closedFormulaFrontierReady_source spec⟩

def ClosedFormulaProvenance.allSubLeft
    {L : Language} {spec : SkolemSpec L}
    {seed : ClosedTerm spec.language}
    {A B : FormulaN L}
    (prior : ClosedFormulaProvenance spec seed A)
    (occurrence : MaxQuantifierOccurrence A)
    (x : Nat) (t : Term L)
    (hSelected :
      occurrence.selected = FormulaN.all x B)
    (prefixMap : ClosedEigenvarMap spec.language)
    (choice : ClosedTerm spec.language)
    (hChoice :
      choice.1 =
        closeSkolemTermWithSeed seed prefixMap
          (liftEigenvarBaseTerm spec t)) :
    ClosedFormulaProvenance spec seed
      (occurrence.replace (formulaSubstN B t x)) :=
  have hChoiceEq :
      choice =
        (⟨closeSkolemTermWithSeed seed prefixMap
            (liftEigenvarBaseTerm spec t),
          closeSkolemTermWithSeed_isClosed seed prefixMap
            (liftEigenvarBaseTerm spec t)⟩ :
          ClosedTerm spec.language) := by
    apply Subtype.ext
    exact hChoice
  by
    cases hChoiceEq
    exact
      ⟨prior.events ++
        [.allSubLeft A B occurrence x t hSelected
          prefixMap
          ⟨closeSkolemTermWithSeed seed prefixMap
              (liftEigenvarBaseTerm spec t),
            closeSkolemTermWithSeed_isClosed seed prefixMap
              (liftEigenvarBaseTerm spec t)⟩ rfl],
      prior.universalMap.insert x
        ⟨closeSkolemTermWithSeed seed prefixMap
            (liftEigenvarBaseTerm spec t),
          closeSkolemTermWithSeed_isClosed seed prefixMap
            (liftEigenvarBaseTerm spec t)⟩,
      .allSubLeft prior.replay occurrence x t hSelected
        prefixMap,
      (closedFormulaAllSubLeft_invariants
        occurrence x t hSelected prior.universalMap
        ⟨closeSkolemTermWithSeed seed prefixMap
            (liftEigenvarBaseTerm spec t),
          closeSkolemTermWithSeed_isClosed seed prefixMap
            (liftEigenvarBaseTerm spec t)⟩
        prior.scopeAligned prior.frontierReady).1,
      (closedFormulaAllSubLeft_invariants
        occurrence x t hSelected prior.universalMap
        ⟨closeSkolemTermWithSeed seed prefixMap
            (liftEigenvarBaseTerm spec t),
          closeSkolemTermWithSeed_isClosed seed prefixMap
            (liftEigenvarBaseTerm spec t)⟩
        prior.scopeAligned prior.frontierReady).2⟩

end LCS.Herbrand.SHGTheorem.Herbrand
end

