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

/-- A construction trace tying final cells and bindings to every exact
equality-free G2nnf Core path step.  The relevant constructor stores membership of the
selected provenance in the predecessor state. -/
inductive ClosedG2nnfLowerTrace
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (seed : ClosedTerm spec.language)
    {Δroot : LCS.Finset (FormulaN L)}
    (root : G2nnfProofTree hNoEq
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot) :
    {Γnode Δnode : LCS.Finset (FormulaN L)} →
    (node : G2nnfProofTree hNoEq Γnode Δnode) →
    G2nnfProofTree.RootToNodePath root node →
    List (ClosedFormulaProvenanceCell spec seed) →
    List (ClosedG2nnfBindingData (hNoEq := hNoEq) spec seed root) → Type where
  | root :
      ClosedG2nnfLowerTrace (hNoEq := hNoEq) spec seed root root (.root root)
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
      {sub : G2nnfProofTree hNoEq
        (((G2nnfRuleCore.allSubLeft A occurrence x B t
          hSelected Gamma Delta).premises)[0]'(by omega)).1
        (((G2nnfRuleCore.allSubLeft A occurrence x B t
          hSelected Gamma Delta).premises)[0]'(by omega)).2}
      {pfx :
        G2nnfProofTree.RootToNodePath root
          (.onePremise
            (.allSubLeft A occurrence x B t hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)}
      {cells : List (ClosedFormulaProvenanceCell spec seed)}
      {bindings :
        List (ClosedG2nnfBindingData (hNoEq := hNoEq) spec seed root)}
      (prior :
        ClosedG2nnfLowerTrace (hNoEq := hNoEq) spec seed root
          (.onePremise
            (.allSubLeft A occurrence x B t hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)
          pfx cells bindings) :
      ClosedG2nnfLowerTrace (hNoEq := hNoEq) spec seed root sub
        (pfx.trans
          (.onePremise
            (.allSubLeft A occurrence x B t hSelected Gamma Delta)
            (by trivial) hPrem hSC sub (.root sub)))
        (closedFormulaProvenanceAllSubLeft
          spec seed (closedG2nnfBindingMap bindings)
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
      {sub : G2nnfProofTree hNoEq
        (((G2nnfRuleCore.allSubRight A occurrence x B y
          hSelected Gamma Delta).premises)[0]'(by omega)).1
        (((G2nnfRuleCore.allSubRight A occurrence x B y
          hSelected Gamma Delta).premises)[0]'(by omega)).2}
      {pfx :
        G2nnfProofTree.RootToNodePath root
          (.onePremise
            (.allSubRight A occurrence x B y hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)}
      {cells : List (ClosedFormulaProvenanceCell spec seed)}
      {bindings :
        List (ClosedG2nnfBindingData (hNoEq := hNoEq) spec seed root)}
      (prior :
        ClosedG2nnfLowerTrace (hNoEq := hNoEq) spec seed root
          (.onePremise
            (.allSubRight A occurrence x B y hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)
          pfx cells bindings) :
      ClosedG2nnfLowerTrace (hNoEq := hNoEq) spec seed root sub
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
      {sub : G2nnfProofTree hNoEq
        (((G2nnfRuleCore.exSubLeft A occurrence x B y
          hSelected Gamma Delta).premises)[0]'(by omega)).1
        (((G2nnfRuleCore.exSubLeft A occurrence x B y
          hSelected Gamma Delta).premises)[0]'(by omega)).2}
      {pfx :
        G2nnfProofTree.RootToNodePath root
          (.onePremise
            (.exSubLeft A occurrence x B y hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)}
      {cells : List (ClosedFormulaProvenanceCell spec seed)}
      {bindings :
        List (ClosedG2nnfBindingData (hNoEq := hNoEq) spec seed root)}
      (priorTrace :
        ClosedG2nnfLowerTrace (hNoEq := hNoEq) spec seed root
          (.onePremise
            (.exSubLeft A occurrence x B y hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)
          pfx cells bindings)
      (hPrefix : AllRulesQuantifierOnPath pfx)
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
            (g2nnfRetentiveAllocationIndex spec
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
                G2nnfExSubLeftOccurrence (hL := hNoEq) root)
              hPrefix))) :
      ClosedG2nnfLowerTrace (hNoEq := hNoEq) spec seed root sub
        (pfx.trans
          (.onePremise
            (.exSubLeft A occurrence x B y hSelected Gamma Delta)
            (by trivial) hPrem hSC sub (.root sub)))
        (closedFormulaProvenanceExSubLeftRelevant
          spec seed A B occurrence x y hSelected hRelevant
          (g2nnfRetentiveAllocationIndex spec
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
              G2nnfExSubLeftOccurrence (hL := hNoEq) root)
            hPrefix)
          prior hScopeCovered Gamma cells)
        (bindings ++
          [makeClosedG2nnfBindingData (hNoEq := hNoEq) spec seed
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
              G2nnfExSubLeftOccurrence (hL := hNoEq) root)
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
      {sub : G2nnfProofTree hNoEq
        (((G2nnfRuleCore.exSubLeft A occurrence x B y
          hSelected Gamma Delta).premises)[0]'(by omega)).1
        (((G2nnfRuleCore.exSubLeft A occurrence x B y
          hSelected Gamma Delta).premises)[0]'(by omega)).2}
      {pfx :
        G2nnfProofTree.RootToNodePath root
          (.onePremise
            (.exSubLeft A occurrence x B y hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)}
      {cells : List (ClosedFormulaProvenanceCell spec seed)}
      {bindings :
        List (ClosedG2nnfBindingData (hNoEq := hNoEq) spec seed root)}
      (prior :
        ClosedG2nnfLowerTrace (hNoEq := hNoEq) spec seed root
          (.onePremise
            (.exSubLeft A occurrence x B y hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)
          pfx cells bindings)
      (hVacuous : x ∉ formulaFVN B) :
      ClosedG2nnfLowerTrace (hNoEq := hNoEq) spec seed root sub
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
      {sub : G2nnfProofTree hNoEq
        (((G2nnfRuleCore.exSubRight A occurrence x B t
          hSelected Gamma Delta).premises)[0]'(by omega)).1
        (((G2nnfRuleCore.exSubRight A occurrence x B t
          hSelected Gamma Delta).premises)[0]'(by omega)).2}
      {pfx :
        G2nnfProofTree.RootToNodePath root
          (.onePremise
            (.exSubRight A occurrence x B t hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)}
      {cells : List (ClosedFormulaProvenanceCell spec seed)}
      {bindings :
        List (ClosedG2nnfBindingData (hNoEq := hNoEq) spec seed root)}
      (prior :
        ClosedG2nnfLowerTrace (hNoEq := hNoEq) spec seed root
          (.onePremise
            (.exSubRight A occurrence x B t hSelected Gamma Delta)
            (by trivial) hPrem hSC sub)
          pfx cells bindings) :
      ClosedG2nnfLowerTrace (hNoEq := hNoEq) spec seed root sub
        (pfx.trans
          (.onePremise
            (.exSubRight A occurrence x B t hSelected Gamma Delta)
            (by trivial) hPrem hSC sub (.root sub)))
        cells bindings

/-- Endpoint-indexed G2nnf state.  The trace prevents arbitrary cells or
bindings from being attached to a path. -/
structure ClosedG2nnfLowerState
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (seed : ClosedTerm spec.language)
    {Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    (root : G2nnfProofTree hNoEq
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot)
    (node : G2nnfProofTree hNoEq Γnode Δnode) where
  path : G2nnfProofTree.RootToNodePath root node
  pathQuantifier : AllRulesQuantifierOnPath path
  pathPure :
    isPureVariableProofG2nnfAux root node path
  formulaProvenance :
    List (ClosedFormulaProvenanceCell spec seed)
  bindings : List (ClosedG2nnfBindingData (hNoEq := hNoEq) spec seed root)
  trace :
    ClosedG2nnfLowerTrace (hNoEq := hNoEq) spec seed root node path
      formulaProvenance bindings
  covers :
    ClosedFormulaProvenanceCovers formulaProvenance Γnode
  live :
    AntecedentVariablesLive
      (closedG2nnfBindingEigenvariables bindings) Γnode
  bindingEigenvariablesNodup :
    (closedG2nnfBindingEigenvariables bindings).Nodup

end LCS.Herbrand.SHGTheorem.Herbrand
end
