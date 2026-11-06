import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.Herbrand.NNFHauptsatz.Equality
import LCS.Herbrand.SHGTheorem.Herbrand.EigenvariablePurity
import LCS.Herbrand.SHGTheorem.Herbrand.ClosedBindings

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

/-- Equality-system Core construction trace, mirroring the five quantifier
transitions of `ClosedG2nnfLowerTrace`. -/
inductive ClosedG2nnfEqLowerTrace
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (seed : ClosedTerm spec.language)
    {Δroot : LCS.Finset (FormulaN L)}
    (root : G2nnfEqProofTree hL
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot) :
    {Γnode Δnode : LCS.Finset (FormulaN L)} →
    (node : G2nnfEqProofTree hL Γnode Δnode) →
    G2nnfEqProofTree.RootToNodePath root node →
    List (ClosedFormulaProvenanceCell spec seed) →
    List (ClosedG2nnfEqBindingData spec seed root) → Type where
  | root :
      ClosedG2nnfEqLowerTrace spec seed root root (.root root)
        [{ formula := spec.source
           provenance :=
             ClosedFormulaProvenance.source spec seed }]
        []
  | allSubLeft
      {A B : FormulaN L}
      {occurrence : MaxQuantifierOccurrence A}
      {x : Nat} {t : Term L}
      {hSelected :
        occurrence.selected = FormulaN.all x B}
      {Gamma Delta : LCS.Finset (FormulaN L)}
      {hPrem :
        ((G2nnfRuleCore.allSubLeft A occurrence x B t
          hSelected Gamma Delta).premises).length = 1}
      {hSC :
        G2nnfRuleCore.SideConditions
          (.allSubLeft A occurrence x B t hSelected Gamma Delta)}
      {sub : G2nnfEqProofTree hL
        (((G2nnfRuleCore.allSubLeft A occurrence x B t
          hSelected Gamma Delta).premises)[0]'(by omega)).1
        (((G2nnfRuleCore.allSubLeft A occurrence x B t
          hSelected Gamma Delta).premises)[0]'(by omega)).2}
      {pfx :
        G2nnfEqProofTree.RootToNodePath root
          (.onePremise
            (.allSubLeft A occurrence x B t hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)}
      {cells : List (ClosedFormulaProvenanceCell spec seed)}
      {bindings :
        List (ClosedG2nnfEqBindingData spec seed root)}
      (prior :
        ClosedG2nnfEqLowerTrace spec seed root
          (.onePremise
            (.allSubLeft A occurrence x B t hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)
          pfx cells bindings) :
      ClosedG2nnfEqLowerTrace spec seed root sub
        (pfx.trans
          (.onePremise
            (.allSubLeft A occurrence x B t hSelected Gamma Delta)
            (by trivial) hPrem hSC sub (.root sub)))
        (closedFormulaProvenanceAllSubLeft
          spec seed (closedG2nnfEqBindingMap bindings)
          A B occurrence x t hSelected Gamma cells)
        bindings
  | allSubRight
      {A B : FormulaN L}
      {occurrence : MaxQuantifierOccurrence A}
      {x y : Nat}
      {hSelected :
        occurrence.selected = FormulaN.all x B}
      {Gamma Delta : LCS.Finset (FormulaN L)}
      {hPrem :
        ((G2nnfRuleCore.allSubRight A occurrence x B y
          hSelected Gamma Delta).premises).length = 1}
      {hSC :
        G2nnfRuleCore.SideConditions
          (.allSubRight A occurrence x B y hSelected Gamma Delta)}
      {sub : G2nnfEqProofTree hL
        (((G2nnfRuleCore.allSubRight A occurrence x B y
          hSelected Gamma Delta).premises)[0]'(by omega)).1
        (((G2nnfRuleCore.allSubRight A occurrence x B y
          hSelected Gamma Delta).premises)[0]'(by omega)).2}
      {pfx :
        G2nnfEqProofTree.RootToNodePath root
          (.onePremise
            (.allSubRight A occurrence x B y hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)}
      {cells : List (ClosedFormulaProvenanceCell spec seed)}
      {bindings :
        List (ClosedG2nnfEqBindingData spec seed root)}
      (prior :
        ClosedG2nnfEqLowerTrace spec seed root
          (.onePremise
            (.allSubRight A occurrence x B y hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)
          pfx cells bindings) :
      ClosedG2nnfEqLowerTrace spec seed root sub
        (pfx.trans
          (.onePremise
            (.allSubRight A occurrence x B y hSelected Gamma Delta)
            (by trivial) hPrem hSC sub (.root sub)))
        cells bindings
  | exSubLeftRelevant
      {A B : FormulaN L}
      {occurrence : MaxQuantifierOccurrence A}
      {x y : Nat}
      {hSelected :
        occurrence.selected = FormulaN.ex x B}
      {Gamma Delta : LCS.Finset (FormulaN L)}
      {hPrem :
        ((G2nnfRuleCore.exSubLeft A occurrence x B y
          hSelected Gamma Delta).premises).length = 1}
      {hSC :
        G2nnfRuleCore.SideConditions
          (.exSubLeft A occurrence x B y hSelected Gamma Delta)}
      {sub : G2nnfEqProofTree hL
        (((G2nnfRuleCore.exSubLeft A occurrence x B y
          hSelected Gamma Delta).premises)[0]'(by omega)).1
        (((G2nnfRuleCore.exSubLeft A occurrence x B y
          hSelected Gamma Delta).premises)[0]'(by omega)).2}
      {pfx :
        G2nnfEqProofTree.RootToNodePath root
          (.onePremise
            (.exSubLeft A occurrence x B y hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)}
      {cells : List (ClosedFormulaProvenanceCell spec seed)}
      {bindings :
        List (ClosedG2nnfEqBindingData spec seed root)}
      (priorTrace :
        ClosedG2nnfEqLowerTrace spec seed root
          (.onePremise
            (.exSubLeft A occurrence x B y hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)
          pfx cells bindings)
      (hPrefix :
        AllRulesQuantifierOnPath_G2nnfEq pfx)
      (hRelevant : x ∈ formulaFVN B)
      (prior :
        ClosedFormulaProvenance spec seed A)
      (hPrior :
        prior ∈
          matchingClosedFormulaProvenances
            spec seed A cells)
      (hScopeCovered :
        prior.universalMap.Covers
          (spec.skolemScope
            (g2nnfEqRetentiveAllocationIndex spec
              ({ ambient := A
                 maxOccurrence := occurrence
                 boundVar := x
                 body := B
                 eigenvariable := y
                 hSelected := hSelected
                 gamma := Gamma
                 delta := Delta
                 hPrem := hPrem
                 hSC := hSC
                 premise := sub
                 path := pfx } :
                G2nnfEqExSubLeftOccurrence root)
              hPrefix))) :
      ClosedG2nnfEqLowerTrace spec seed root sub
        (pfx.trans
          (.onePremise
            (.exSubLeft A occurrence x B y hSelected Gamma Delta)
            (by trivial) hPrem hSC sub (.root sub)))
        (closedFormulaProvenanceExSubLeftRelevant
          spec seed A B occurrence x y hSelected hRelevant
          (g2nnfEqRetentiveAllocationIndex spec
            ({ ambient := A
               maxOccurrence := occurrence
               boundVar := x
               body := B
               eigenvariable := y
               hSelected := hSelected
               gamma := Gamma
               delta := Delta
               hPrem := hPrem
               hSC := hSC
               premise := sub
               path := pfx } :
              G2nnfEqExSubLeftOccurrence root)
            hPrefix)
          prior hScopeCovered Gamma cells)
        (bindings ++
          [makeClosedG2nnfEqBindingData spec seed
            ({ ambient := A
               maxOccurrence := occurrence
               boundVar := x
               body := B
               eigenvariable := y
               hSelected := hSelected
               gamma := Gamma
               delta := Delta
               hPrem := hPrem
               hSC := hSC
               premise := sub
               path := pfx } :
              G2nnfEqExSubLeftOccurrence root)
            hPrefix hRelevant prior hScopeCovered])
  | exSubLeftVacuous
      {A B : FormulaN L}
      {occurrence : MaxQuantifierOccurrence A}
      {x y : Nat}
      {hSelected :
        occurrence.selected = FormulaN.ex x B}
      {Gamma Delta : LCS.Finset (FormulaN L)}
      {hPrem :
        ((G2nnfRuleCore.exSubLeft A occurrence x B y
          hSelected Gamma Delta).premises).length = 1}
      {hSC :
        G2nnfRuleCore.SideConditions
          (.exSubLeft A occurrence x B y hSelected Gamma Delta)}
      {sub : G2nnfEqProofTree hL
        (((G2nnfRuleCore.exSubLeft A occurrence x B y
          hSelected Gamma Delta).premises)[0]'(by omega)).1
        (((G2nnfRuleCore.exSubLeft A occurrence x B y
          hSelected Gamma Delta).premises)[0]'(by omega)).2}
      {pfx :
        G2nnfEqProofTree.RootToNodePath root
          (.onePremise
            (.exSubLeft A occurrence x B y hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)}
      {cells : List (ClosedFormulaProvenanceCell spec seed)}
      {bindings :
        List (ClosedG2nnfEqBindingData spec seed root)}
      (prior :
        ClosedG2nnfEqLowerTrace spec seed root
          (.onePremise
            (.exSubLeft A occurrence x B y hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)
          pfx cells bindings)
      (hVacuous : x ∉ formulaFVN B) :
      ClosedG2nnfEqLowerTrace spec seed root sub
        (pfx.trans
          (.onePremise
            (.exSubLeft A occurrence x B y hSelected Gamma Delta)
            (by trivial) hPrem hSC sub (.root sub)))
        (closedFormulaProvenanceExSubLeftVacuous
          spec seed A B occurrence x y hSelected hVacuous
          Gamma cells)
        bindings
  | exSubRight
      {A B : FormulaN L}
      {occurrence : MaxQuantifierOccurrence A}
      {x : Nat} {t : Term L}
      {hSelected :
        occurrence.selected = FormulaN.ex x B}
      {Gamma Delta : LCS.Finset (FormulaN L)}
      {hPrem :
        ((G2nnfRuleCore.exSubRight A occurrence x B t
          hSelected Gamma Delta).premises).length = 1}
      {hSC :
        G2nnfRuleCore.SideConditions
          (.exSubRight A occurrence x B t hSelected Gamma Delta)}
      {sub : G2nnfEqProofTree hL
        (((G2nnfRuleCore.exSubRight A occurrence x B t
          hSelected Gamma Delta).premises)[0]'(by omega)).1
        (((G2nnfRuleCore.exSubRight A occurrence x B t
          hSelected Gamma Delta).premises)[0]'(by omega)).2}
      {pfx :
        G2nnfEqProofTree.RootToNodePath root
          (.onePremise
            (.exSubRight A occurrence x B t hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)}
      {cells : List (ClosedFormulaProvenanceCell spec seed)}
      {bindings :
        List (ClosedG2nnfEqBindingData spec seed root)}
      (prior :
        ClosedG2nnfEqLowerTrace spec seed root
          (.onePremise
            (.exSubRight A occurrence x B t hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)
          pfx cells bindings) :
      ClosedG2nnfEqLowerTrace spec seed root sub
        (pfx.trans
          (.onePremise
            (.exSubRight A occurrence x B t hSelected Gamma Delta)
            (by trivial) hPrem hSC sub (.root sub)))
        cells bindings

/-- Endpoint-indexed equality-system state. -/
structure ClosedG2nnfEqLowerState
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (seed : ClosedTerm spec.language)
    {Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    (root : G2nnfEqProofTree hL
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot)
    (node : G2nnfEqProofTree hL Γnode Δnode) where
  path : G2nnfEqProofTree.RootToNodePath root node
  pathQuantifier :
    AllRulesQuantifierOnPath_G2nnfEq path
  pathPure :
    isPureVariableProof_G2nnfEqAux root node path
  formulaProvenance :
    List (ClosedFormulaProvenanceCell spec seed)
  bindings :
    List (ClosedG2nnfEqBindingData spec seed root)
  trace :
    ClosedG2nnfEqLowerTrace spec seed root node path
      formulaProvenance bindings
  covers :
    ClosedFormulaProvenanceCovers formulaProvenance Γnode
  live :
    AntecedentVariablesLive
      (closedG2nnfEqBindingEigenvariables bindings) Γnode
  bindingEigenvariablesNodup :
    (closedG2nnfEqBindingEigenvariables bindings).Nodup

/-- Equality-system nonempty exact-path family. -/
structure ClosedG2nnfEqLowerStateFamily
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (seed : ClosedTerm spec.language)
    {Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    (root : G2nnfEqProofTree hL
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot)
    (node : G2nnfEqProofTree hL Γnode Δnode)
    (path : G2nnfEqProofTree.RootToNodePath root node) where
  states :
    List (ClosedG2nnfEqLowerState spec seed root node)
  nonempty : states ≠ []
  exactPath :
    ∀ state, state ∈ states → state.path = path

end LCS.Herbrand.SHGTheorem.Herbrand
end
