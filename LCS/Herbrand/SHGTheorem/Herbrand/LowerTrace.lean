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
import LCS.Herbrand.SHGTheorem.Herbrand.ScopeAndPurity
import LCS.Herbrand.SHGTheorem.Herbrand.Provenance

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

private def ClosedG2nnfLowerState.eigenMap
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {spec : SkolemSpec L}
    {seed : ClosedTerm spec.language}
    {Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hNoEq
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot}
    {node : G2nnfProofTree hNoEq Γnode Δnode}
    (state : ClosedG2nnfLowerState (hNoEq := hNoEq) spec seed root node) :
    ClosedEigenvarMap spec.language :=
  closedG2nnfBindingMap state.bindings

private def ClosedG2nnfLowerState.initial
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (seed : ClosedTerm spec.language)
    {Δroot : LCS.Finset (FormulaN L)}
    (root : G2nnfProofTree hNoEq
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot)
    (hPure : IsPureVariableProofG2nnf root) :
    ClosedG2nnfLowerState (hNoEq := hNoEq) spec seed root root :=
  { path := .root root
    pathQuantifier := trivial
    pathPure := hPure
    formulaProvenance :=
      [{ formula := spec.source
         provenance := ClosedFormulaProvenance.source spec seed }]
    bindings := []
    trace := .root
    covers := by
      intro A hA
      have hEq : A = spec.source :=
        (LCS.Finset.mem_singleton A spec.source).mp hA
      subst A
      exact
        ⟨{ formula := spec.source
           provenance :=
             ClosedFormulaProvenance.source spec seed },
          by simp, rfl⟩
    live := by
      intro y hy
      simp [closedG2nnfBindingEigenvariables] at hy
    bindingEigenvariablesNodup := List.nodup_nil }

/-- Equality-system Core construction trace, mirroring the five quantifier
transitions of `ClosedG2nnfLowerTrace`. -/
private inductive ClosedG2nnfEqLowerTrace
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

private def ClosedG2nnfEqLowerState.eigenMap
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {spec : SkolemSpec L}
    {seed : ClosedTerm spec.language}
    {Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot}
    {node : G2nnfEqProofTree hL Γnode Δnode}
    (state :
      ClosedG2nnfEqLowerState spec seed root node) :
    ClosedEigenvarMap spec.language :=
  closedG2nnfEqBindingMap state.bindings

def ClosedG2nnfEqLowerState.initial
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (seed : ClosedTerm spec.language)
    {Δroot : LCS.Finset (FormulaN L)}
    (root : G2nnfEqProofTree hL
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot)
    (hPure : IsPureVariableProof_G2nnfEq root) :
    ClosedG2nnfEqLowerState spec seed root root :=
  { path := .root root
    pathQuantifier := trivial
    pathPure := hPure
    formulaProvenance :=
      [{ formula := spec.source
         provenance := ClosedFormulaProvenance.source spec seed }]
    bindings := []
    trace := .root
    covers := by
      intro A hA
      have hEq : A = spec.source :=
        (LCS.Finset.mem_singleton A spec.source).mp hA
      subst A
      exact
        ⟨{ formula := spec.source
           provenance :=
             ClosedFormulaProvenance.source spec seed },
          by simp, rfl⟩
    live := by
      intro y hy
      simp [closedG2nnfEqBindingEigenvariables] at hy
    bindingEigenvariablesNodup := List.nodup_nil }

/-- Quantifier-only path evidence composes along exact G2nnf occurrence
paths. -/
private theorem allRulesQuantifierOnPath_trans
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γmid Δmid Γnode Δnode :
      LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hNoEq Γroot Δroot}
    {mid : G2nnfProofTree hNoEq Γmid Δmid}
    {node : G2nnfProofTree hNoEq Γnode Δnode}
    (first : G2nnfProofTree.RootToNodePath root mid)
    (second : G2nnfProofTree.RootToNodePath mid node)
    (hFirst : AllRulesQuantifierOnPath first)
    (hSecond : AllRulesQuantifierOnPath second) :
    AllRulesQuantifierOnPath (first.trans second) := by
  induction first with
  | root _ =>
      exact hSecond
  | onePremise rule hAdmit hPrem hSC sub path ih =>
      exact ⟨hFirst.1, ih second hFirst.2 hSecond⟩
  | leftPremise rule hAdmit hPrem hSC sub₁ sub₂ path ih =>
      exact ⟨hFirst.1, ih second hFirst.2 hSecond⟩
  | rightPremise rule hAdmit hPrem hSC sub₁ sub₂ path ih =>
      exact ⟨hFirst.1, ih second hFirst.2 hSecond⟩

/-- Equality-system path composition. -/
private theorem allRulesQuantifierOnPathEq_trans
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γmid Δmid Γnode Δnode :
      LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL Γroot Δroot}
    {mid : G2nnfEqProofTree hL Γmid Δmid}
    {node : G2nnfEqProofTree hL Γnode Δnode}
    (first : G2nnfEqProofTree.RootToNodePath root mid)
    (second : G2nnfEqProofTree.RootToNodePath mid node)
    (hFirst : AllRulesQuantifierOnPath_G2nnfEq first)
    (hSecond : AllRulesQuantifierOnPath_G2nnfEq second) :
    AllRulesQuantifierOnPath_G2nnfEq
      (first.trans second) := by
  induction first with
  | root _ =>
      exact hSecond
  | onePremise rule hAdmit hPrem hSC sub path ih =>
      exact ⟨hFirst.1, ih second hFirst.2 hSecond⟩
  | leftPremise rule hAdmit hPrem hSC sub₁ sub₂ path ih =>
      exact ⟨hFirst.1, ih second hFirst.2 hSecond⟩
  | rightPremise rule hAdmit hPrem hSC sub₁ sub₂ path ih =>
      exact ⟨hFirst.1, ih second hFirst.2 hSecond⟩

/-- Right identity and associativity for occurrence-sensitive G2nnf path
composition. -/
private theorem g2nnfPath_trans_root
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hNoEq Γroot Δroot}
    {node : G2nnfProofTree hNoEq Γnode Δnode}
    (path : G2nnfProofTree.RootToNodePath root node) :
    path.trans (.root node) = path := by
  induction path with
  | root _ =>
      rfl
  | onePremise rule hAdmit hPrem hSC sub tail ih =>
      simp [G2nnfProofTree.RootToNodePath.trans, ih]
  | leftPremise rule hAdmit hPrem hSC sub₁ sub₂ tail ih =>
      simp [G2nnfProofTree.RootToNodePath.trans, ih]
  | rightPremise rule hAdmit hPrem hSC sub₁ sub₂ tail ih =>
      simp [G2nnfProofTree.RootToNodePath.trans, ih]

private theorem g2nnfPath_trans_assoc
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γ₁ Δ₁ Γ₂ Δ₂ Γ₃ Δ₃ Γ₄ Δ₄ :
      LCS.Finset (FormulaN L)}
    {T₁ : G2nnfProofTree hNoEq Γ₁ Δ₁}
    {T₂ : G2nnfProofTree hNoEq Γ₂ Δ₂}
    {T₃ : G2nnfProofTree hNoEq Γ₃ Δ₃}
    {T₄ : G2nnfProofTree hNoEq Γ₄ Δ₄}
    (first : G2nnfProofTree.RootToNodePath T₁ T₂)
    (second : G2nnfProofTree.RootToNodePath T₂ T₃)
    (third : G2nnfProofTree.RootToNodePath T₃ T₄) :
    (first.trans second).trans third =
      first.trans (second.trans third) := by
  induction first with
  | root _ =>
      rfl
  | onePremise rule hAdmit hPrem hSC sub tail ih =>
      simp [G2nnfProofTree.RootToNodePath.trans, ih]
  | leftPremise rule hAdmit hPrem hSC sub₁ sub₂ tail ih =>
      simp [G2nnfProofTree.RootToNodePath.trans, ih]
  | rightPremise rule hAdmit hPrem hSC sub₁ sub₂ tail ih =>
      simp [G2nnfProofTree.RootToNodePath.trans, ih]

/-- Equality-system path laws. -/
private theorem g2nnfEqPath_trans_root
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL Γroot Δroot}
    {node : G2nnfEqProofTree hL Γnode Δnode}
    (path : G2nnfEqProofTree.RootToNodePath root node) :
    path.trans (.root node) = path := by
  induction path with
  | root _ =>
      rfl
  | onePremise rule hAdmit hPrem hSC sub tail ih =>
      simp [G2nnfEqProofTree.RootToNodePath.trans, ih]
  | leftPremise rule hAdmit hPrem hSC sub₁ sub₂ tail ih =>
      simp [G2nnfEqProofTree.RootToNodePath.trans, ih]
  | rightPremise rule hAdmit hPrem hSC sub₁ sub₂ tail ih =>
      simp [G2nnfEqProofTree.RootToNodePath.trans, ih]

private theorem g2nnfEqPath_trans_assoc
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γ₁ Δ₁ Γ₂ Δ₂ Γ₃ Δ₃ Γ₄ Δ₄ :
      LCS.Finset (FormulaN L)}
    {T₁ : G2nnfEqProofTree hL Γ₁ Δ₁}
    {T₂ : G2nnfEqProofTree hL Γ₂ Δ₂}
    {T₃ : G2nnfEqProofTree hL Γ₃ Δ₃}
    {T₄ : G2nnfEqProofTree hL Γ₄ Δ₄}
    (first : G2nnfEqProofTree.RootToNodePath T₁ T₂)
    (second : G2nnfEqProofTree.RootToNodePath T₂ T₃)
    (third : G2nnfEqProofTree.RootToNodePath T₃ T₄) :
    (first.trans second).trans third =
      first.trans (second.trans third) := by
  induction first with
  | root _ =>
      rfl
  | onePremise rule hAdmit hPrem hSC sub tail ih =>
      simp [G2nnfEqProofTree.RootToNodePath.trans, ih]
  | leftPremise rule hAdmit hPrem hSC sub₁ sub₂ tail ih =>
      simp [G2nnfEqProofTree.RootToNodePath.trans, ih]
  | rightPremise rule hAdmit hPrem hSC sub₁ sub₂ tail ih =>
      simp [G2nnfEqProofTree.RootToNodePath.trans, ih]

/-- A nonempty family of equality-free endpoint states, all certified to
have the supplied exact root-to-node path. -/
private structure ClosedG2nnfLowerStateFamily
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (seed : ClosedTerm spec.language)
    {Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    (root : G2nnfProofTree hNoEq
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot)
    (node : G2nnfProofTree hNoEq Γnode Δnode)
    (path : G2nnfProofTree.RootToNodePath root node) where
  states : List (ClosedG2nnfLowerState (hNoEq := hNoEq) spec seed root node)
  nonempty : states ≠ []
  exactPath :
    ∀ state, state ∈ states → state.path = path

private def ClosedG2nnfLowerStateFamily.join
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {spec : SkolemSpec L}
    {seed : ClosedTerm spec.language}
    {Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hNoEq
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot}
    {node : G2nnfProofTree hNoEq Γnode Δnode}
    {path : G2nnfProofTree.RootToNodePath root node}
    (families :
      List
        (ClosedG2nnfLowerStateFamily (hNoEq := hNoEq)
          spec seed root node path))
    (hFamilies : families ≠ []) :
    ClosedG2nnfLowerStateFamily (hNoEq := hNoEq) spec seed root node path :=
  { states := families.flatMap (fun family => family.states)
    nonempty := by
      intro hEmpty
      have hAllEmpty :
          ∀ family, family ∈ families →
            family.states = [] := by
        intro family hFamily
        apply Classical.byContradiction
        intro hFamilyStates
        obtain ⟨state, hState⟩ :=
          List.exists_mem_of_ne_nil _ hFamilyStates
        have hStateFlat :
            state ∈
              families.flatMap
                (fun branch => branch.states) :=
          List.mem_flatMap.mpr
            ⟨family, hFamily, hState⟩
        rw [hEmpty] at hStateFlat
        simp at hStateFlat
      obtain ⟨family, hFamily⟩ :=
        List.exists_mem_of_ne_nil _ hFamilies
      exact family.nonempty (hAllEmpty family hFamily)
    exactPath := by
      intro state hState
      obtain ⟨family, hFamily, hStateFamily⟩ :=
        List.mem_flatMap.mp hState
      exact family.exactPath state hStateFamily }

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

private def ClosedG2nnfEqLowerStateFamily.join
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {spec : SkolemSpec L}
    {seed : ClosedTerm spec.language}
    {Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot}
    {node : G2nnfEqProofTree hL Γnode Δnode}
    {path : G2nnfEqProofTree.RootToNodePath root node}
    (families :
      List
        (ClosedG2nnfEqLowerStateFamily
          spec seed root node path))
    (hFamilies : families ≠ []) :
    ClosedG2nnfEqLowerStateFamily spec seed root node path :=
  { states := families.flatMap (fun family => family.states)
    nonempty := by
      intro hEmpty
      have hAllEmpty :
          ∀ family, family ∈ families →
            family.states = [] := by
        intro family hFamily
        apply Classical.byContradiction
        intro hFamilyStates
        obtain ⟨state, hState⟩ :=
          List.exists_mem_of_ne_nil _ hFamilyStates
        have hStateFlat :
            state ∈
              families.flatMap
                (fun branch => branch.states) :=
          List.mem_flatMap.mpr
            ⟨family, hFamily, hState⟩
        rw [hEmpty] at hStateFlat
        simp at hStateFlat
      obtain ⟨family, hFamily⟩ :=
        List.exists_mem_of_ne_nil _ hFamilies
      exact family.nonempty (hAllEmpty family hFamily)
    exactPath := by
      intro state hState
      obtain ⟨family, hFamily, hStateFamily⟩ :=
        List.mem_flatMap.mp hState
      exact family.exactPath state hStateFamily }

/-- Structural fold over an equality-free G2nnf Core path. Recursion uses
only the supplied path, so no auxiliary depth or fuel can diverge from it. -/
private noncomputable def buildClosedG2nnfLowerStateAux
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (seed : ClosedTerm spec.language)
    {Δroot Γcur Δcur : LCS.Finset (FormulaN L)}
    (root : G2nnfProofTree hNoEq
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot)
    {current : G2nnfProofTree hNoEq Γcur Δcur}
    (state : ClosedG2nnfLowerState (hNoEq := hNoEq) spec seed root current)
    {Γnode Δnode : LCS.Finset (FormulaN L)}
    {node : G2nnfProofTree hNoEq Γnode Δnode}
    (path : G2nnfProofTree.RootToNodePath current node)
    (hQuantifier : AllRulesQuantifierOnPath path) :
    ClosedG2nnfLowerStateFamily (hNoEq := hNoEq) spec seed root node
      (state.path.trans path) := by
  induction path with
  | root T =>
      refine
        { states := [state]
          nonempty := by simp
          exactPath := ?_ }
      intro finalState hFinalState
      have hEq : finalState = state := by
        simpa using hFinalState
      subst finalState
      exact (g2nnfPath_trans_root state.path).symm
  | onePremise rule hAdmit hPrem hSC sub tail ih =>
      rcases hQuantifier with ⟨hRule, hTail⟩
      let step :
          G2nnfProofTree.RootToNodePath
            (.onePremise rule hAdmit hPrem hSC sub) sub :=
        .onePremise rule hAdmit hPrem hSC sub (.root sub)
      let subPrefix :
          G2nnfProofTree.RootToNodePath root sub :=
        state.path.trans step
      have hStep : AllRulesQuantifierOnPath step :=
        ⟨hRule, trivial⟩
      have hSubPrefix :
          AllRulesQuantifierOnPath subPrefix :=
        allRulesQuantifierOnPath_trans
          state.path step state.pathQuantifier hStep
      cases rule with
      | allSubLeft A occurrence x B t hSelected Gamma Delta =>
          simp only [G2nnfRuleCore.isQuantifierRule] at hRule
          have hPureSub :
              isPureVariableProofG2nnfAux root sub subPrefix := by
            simpa [subPrefix, step] using state.pathPure.2
          have hLiveSub :
              AntecedentVariablesLive
                (closedG2nnfBindingEigenvariables state.bindings)
                (((G2nnfRuleCore.allSubLeft
                  A occurrence x B t hSelected Gamma Delta).premises)[0]'(by omega)).1 :=
            g2nnfQuantifierPremise_preserves_live
              (.allSubLeft A occurrence x B t hSelected Gamma Delta)
              hPrem hRule state.live
          let nextCells :=
            closedFormulaProvenanceAllSubLeft
              spec seed state.eigenMap A B occurrence x t
              hSelected Gamma state.formulaProvenance
          have hCoversSub :
              ClosedFormulaProvenanceCovers nextCells
                (((G2nnfRuleCore.allSubLeft
                  A occurrence x B t hSelected Gamma Delta).premises)[0]'(by omega)).1 :=
            closedFormulaProvenanceAllSubLeft_covers
              spec seed state.eigenMap A B occurrence x t
              hSelected Gamma state.formulaProvenance
              state.covers
          let nextState :
              ClosedG2nnfLowerState (hNoEq := hNoEq) spec seed root sub :=
            { path := subPrefix
              pathQuantifier := hSubPrefix
              pathPure := hPureSub
              formulaProvenance := nextCells
              bindings := state.bindings
              trace := .allSubLeft state.trace
              covers := hCoversSub
              live := hLiveSub
              bindingEigenvariablesNodup :=
                state.bindingEigenvariablesNodup }
          have result := ih nextState hTail
          simpa [nextState, subPrefix, step,
            G2nnfProofTree.RootToNodePath.trans,
            g2nnfPath_trans_assoc] using result
      | allSubRight A occurrence x B y hSelected Gamma Delta =>
          simp only [G2nnfRuleCore.isQuantifierRule] at hRule
          have hPureSub :
              isPureVariableProofG2nnfAux root sub subPrefix := by
            simpa [subPrefix, step] using state.pathPure.2
          have hLiveSub :
              AntecedentVariablesLive
                (closedG2nnfBindingEigenvariables state.bindings)
                (((G2nnfRuleCore.allSubRight
                  A occurrence x B y hSelected Gamma Delta).premises)[0]'(by omega)).1 :=
            g2nnfQuantifierPremise_preserves_live
              (.allSubRight A occurrence x B y hSelected Gamma Delta)
              hPrem hRule state.live
          let nextState :
              ClosedG2nnfLowerState (hNoEq := hNoEq) spec seed root sub :=
            { path := subPrefix
              pathQuantifier := hSubPrefix
              pathPure := hPureSub
              formulaProvenance := state.formulaProvenance
              bindings := state.bindings
              trace := .allSubRight state.trace
              covers := state.covers
              live := hLiveSub
              bindingEigenvariablesNodup :=
                state.bindingEigenvariablesNodup }
          have result := ih nextState hTail
          simpa [nextState, subPrefix, step,
            G2nnfProofTree.RootToNodePath.trans,
            g2nnfPath_trans_assoc] using result
      | exSubLeft A occurrence x B y hSelected Gamma Delta =>
          simp only [G2nnfRuleCore.isQuantifierRule] at hRule
          let exactOccurrence : G2nnfExSubLeftOccurrence (hL := hNoEq) root :=
            { ambient := A
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
              path := state.path }
          classical
          by_cases hRelevant : x ∈ formulaFVN B
          · have hPurityStep :=
              g2nnfExSubLeft_purity_step
                A B occurrence x y hSelected Gamma Delta
                hPrem hSC sub state.path state.pathPure
            have hFresh :
                y ∉
                  closedG2nnfBindingEigenvariables
                    state.bindings :=
              not_mem_of_g2nnfSequentVariableFree_of_live
                hPurityStep.1 state.live
            have hLiveSub :
                AntecedentVariablesLive
                  (closedG2nnfBindingEigenvariables state.bindings)
                  (((G2nnfRuleCore.exSubLeft
                    A occurrence x B y hSelected Gamma Delta).premises)[0]'(by omega)).1 :=
              g2nnfQuantifierPremise_preserves_live
                (.exSubLeft A occurrence x B y hSelected Gamma Delta)
                hPrem hRule state.live
            have hWitness :=
              g2nnfExSubLeft_eigenvariable_witness
                A B occurrence x y hSelected Gamma Delta
                hSC hRelevant
            let i : Fin spec.n :=
              g2nnfRetentiveAllocationIndex
                spec exactOccurrence state.pathQuantifier
            let hBinding :
                G2nnfRetentiveAllocationBinding
                  spec exactOccurrence i :=
              g2nnfRetentiveAllocationIndex_binding
                spec exactOccurrence state.pathQuantifier hRelevant
            let principals :=
              matchingClosedFormulaProvenances
                spec seed A state.formulaProvenance
            have hPrincipalExists :
                ∃ provenance, provenance ∈ principals := by
              simpa [principals] using
                matchingClosedFormulaProvenances_nonempty_of_covers
                  state.covers A
                  (LCS.Finset.mem_insert.mpr (Or.inl rfl))
            have hPrincipals : principals ≠ [] := by
              intro hNil
              obtain ⟨provenance, hProvenance⟩ :=
                hPrincipalExists
              rw [hNil] at hProvenance
              simp at hProvenance
            let branch :
                (selected : {provenance //
                  provenance ∈ principals}) →
                  ClosedG2nnfLowerStateFamily (hNoEq := hNoEq) spec seed root _
                    (state.path.trans
                      (.onePremise
                        (.exSubLeft A occurrence x B y hSelected Gamma Delta)
                        hAdmit hPrem hSC sub tail)) :=
              fun selected => by
                let prior := selected.1
                have hPrior :
                    prior ∈
                      matchingClosedFormulaProvenances
                        spec seed A state.formulaProvenance := by
                  simpa [prior, principals] using selected.2
                have hScopeCovered :
                    prior.universalMap.Covers
                      (spec.skolemScope i) :=
                  closedFormulaProvenance_scopeCovered_g2nnf
                    exactOccurrence i hBinding prior
                let data :
                    ClosedG2nnfBindingData (hNoEq := hNoEq) spec seed root :=
                  makeClosedG2nnfBindingData
                    spec seed exactOccurrence state.pathQuantifier
                    hRelevant prior hScopeCovered
                let nextCells :=
                  closedFormulaProvenanceExSubLeftRelevant
                    spec seed A B occurrence x y hSelected
                    hRelevant i prior hScopeCovered Gamma
                    state.formulaProvenance
                have hCoversSub :
                    ClosedFormulaProvenanceCovers nextCells
                      (((G2nnfRuleCore.exSubLeft
                        A occurrence x B y hSelected Gamma Delta).premises)[0]'(by omega)).1 :=
                  closedFormulaProvenanceExSubLeftRelevant_covers
                    spec seed A B occurrence x y hSelected
                    hRelevant i prior hScopeCovered Gamma
                    state.formulaProvenance state.covers
                have hLiveNext :
                    AntecedentVariablesLive
                      (closedG2nnfBindingEigenvariables
                        (state.bindings ++ [data]))
                      (((G2nnfRuleCore.exSubLeft
                        A occurrence x B y hSelected Gamma Delta).premises)[0]'(by omega)).1 := by
                  have hVariables :
                      closedG2nnfBindingEigenvariables
                          (state.bindings ++ [data]) =
                        closedG2nnfBindingEigenvariables
                            state.bindings ++ [y] := by
                    simp [closedG2nnfBindingEigenvariables,
                      data, makeClosedG2nnfBindingData,
                      exactOccurrence]
                  rw [hVariables]
                  exact
                    antecedentVariablesLive_append_singleton
                      hLiveSub hWitness
                have hNodup :
                    (closedG2nnfBindingEigenvariables
                      (state.bindings ++ [data])).Nodup := by
                  have hVariables :
                      closedG2nnfBindingEigenvariables
                          (state.bindings ++ [data]) =
                        closedG2nnfBindingEigenvariables
                            state.bindings ++ [y] := by
                    simp [closedG2nnfBindingEigenvariables,
                      data, makeClosedG2nnfBindingData,
                      exactOccurrence]
                  rw [hVariables, List.nodup_append]
                  refine
                    ⟨state.bindingEigenvariablesNodup,
                      by simp, ?_⟩
                  intro a ha b hb hab
                  have hby : b = y :=
                    List.mem_singleton.mp hb
                  subst b
                  subst a
                  exact hFresh ha
                let nextState :
                    ClosedG2nnfLowerState (hNoEq := hNoEq) spec seed root sub :=
                  { path := subPrefix
                    pathQuantifier := hSubPrefix
                    pathPure := by
                      simpa [subPrefix, step] using
                        hPurityStep.2
                    formulaProvenance := nextCells
                    bindings := state.bindings ++ [data]
                    trace :=
                      .exSubLeftRelevant state.trace
                        state.pathQuantifier hRelevant prior hPrior
                        hScopeCovered
                    covers := hCoversSub
                    live := hLiveNext
                    bindingEigenvariablesNodup := hNodup }
                have result := ih nextState hTail
                simpa [nextState, subPrefix, step,
                  G2nnfProofTree.RootToNodePath.trans,
                  g2nnfPath_trans_assoc] using result
            let families :=
              principals.attach.map branch
            have hFamilies : families ≠ [] := by
              simpa [families] using hPrincipals
            exact
              ClosedG2nnfLowerStateFamily.join
                families hFamilies
          · have hPureSub :
                isPureVariableProofG2nnfAux root sub subPrefix := by
              simpa [subPrefix, step] using state.pathPure.2
            have hLiveSub :
                AntecedentVariablesLive
                  (closedG2nnfBindingEigenvariables state.bindings)
                  (((G2nnfRuleCore.exSubLeft
                    A occurrence x B y hSelected Gamma Delta).premises)[0]'(by omega)).1 :=
              g2nnfQuantifierPremise_preserves_live
                (.exSubLeft A occurrence x B y hSelected Gamma Delta)
                hPrem hRule state.live
            let nextCells :=
              closedFormulaProvenanceExSubLeftVacuous
                spec seed A B occurrence x y hSelected
                hRelevant Gamma state.formulaProvenance
            have hCoversSub :
                ClosedFormulaProvenanceCovers nextCells
                  (((G2nnfRuleCore.exSubLeft
                    A occurrence x B y hSelected Gamma Delta).premises)[0]'(by omega)).1 :=
              closedFormulaProvenanceExSubLeftVacuous_covers
                spec seed A B occurrence x y hSelected
                hRelevant Gamma state.formulaProvenance
                state.covers
            let nextState :
                ClosedG2nnfLowerState (hNoEq := hNoEq) spec seed root sub :=
              { path := subPrefix
                pathQuantifier := hSubPrefix
                pathPure := hPureSub
                formulaProvenance := nextCells
                bindings := state.bindings
                trace :=
                  .exSubLeftVacuous state.trace hRelevant
                covers := hCoversSub
                live := hLiveSub
                bindingEigenvariablesNodup :=
                  state.bindingEigenvariablesNodup }
            have result := ih nextState hTail
            simpa [nextState, subPrefix, step,
              G2nnfProofTree.RootToNodePath.trans,
              g2nnfPath_trans_assoc] using result
      | exSubRight A occurrence x B t hSelected Gamma Delta =>
          simp only [G2nnfRuleCore.isQuantifierRule] at hRule
          have hPureSub :
              isPureVariableProofG2nnfAux root sub subPrefix := by
            simpa [subPrefix, step] using state.pathPure.2
          have hLiveSub :
              AntecedentVariablesLive
                (closedG2nnfBindingEigenvariables state.bindings)
                (((G2nnfRuleCore.exSubRight
                  A occurrence x B t hSelected Gamma Delta).premises)[0]'(by omega)).1 :=
            g2nnfQuantifierPremise_preserves_live
              (.exSubRight A occurrence x B t hSelected Gamma Delta)
              hPrem hRule state.live
          let nextState :
              ClosedG2nnfLowerState (hNoEq := hNoEq) spec seed root sub :=
            { path := subPrefix
              pathQuantifier := hSubPrefix
              pathPure := hPureSub
              formulaProvenance := state.formulaProvenance
              bindings := state.bindings
              trace := .exSubRight state.trace
              covers := state.covers
              live := hLiveSub
              bindingEigenvariablesNodup :=
                state.bindingEigenvariablesNodup }
          have result := ih nextState hTail
          simpa [nextState, subPrefix, step,
            G2nnfProofTree.RootToNodePath.trans,
            g2nnfPath_trans_assoc] using result
      | _ =>
          simp_all [G2nnfRuleCore.isQuantifierRule]
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

/-- Certified nonempty G2nnf result for one exact lower path. -/
private noncomputable def buildClosedG2nnfLowerStates
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (seed : ClosedTerm spec.language)
    {Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    (root : G2nnfProofTree hNoEq
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot)
    {node : G2nnfProofTree hNoEq Γnode Δnode}
    (path : G2nnfProofTree.RootToNodePath root node)
    (hQuantifier : AllRulesQuantifierOnPath path)
    (hPure : IsPureVariableProofG2nnf root) :
    ClosedG2nnfLowerStateFamily (hNoEq := hNoEq) spec seed root node path := by
  let initial :=
    ClosedG2nnfLowerState.initial spec seed root hPure
  have result :=
    buildClosedG2nnfLowerStateAux
      spec seed root initial path hQuantifier
  simpa [initial, ClosedG2nnfLowerState.initial,
    G2nnfProofTree.RootToNodePath.trans] using result

/-- Direct structural equality-system Core fold with the same state transitions
and selected-lineage discipline as the base system. -/
noncomputable def buildClosedG2nnfEqLowerStateAux
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    (seed : ClosedTerm spec.language)
    {Δroot Γcur Δcur : LCS.Finset (FormulaN L)}
    (root : G2nnfEqProofTree hL
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot)
    {current : G2nnfEqProofTree hL Γcur Δcur}
    (state :
      ClosedG2nnfEqLowerState spec seed root current)
    {Γnode Δnode : LCS.Finset (FormulaN L)}
    {node : G2nnfEqProofTree hL Γnode Δnode}
    (path :
      G2nnfEqProofTree.RootToNodePath current node)
    (hQuantifier :
      AllRulesQuantifierOnPath_G2nnfEq path) :
    ClosedG2nnfEqLowerStateFamily spec seed root node
      (state.path.trans path) := by
  induction path with
  | root T =>
      refine
        { states := [state]
          nonempty := by simp
          exactPath := ?_ }
      intro finalState hFinalState
      have hEq : finalState = state := by
        simpa using hFinalState
      subst finalState
      exact (g2nnfEqPath_trans_root state.path).symm
  | onePremise rule hAdmit hPrem hSC sub tail ih =>
      rcases hQuantifier with ⟨hRule, hTail⟩
      let step :
          G2nnfEqProofTree.RootToNodePath
            (.onePremise rule hAdmit hPrem hSC sub) sub :=
        .onePremise rule hAdmit hPrem hSC sub (.root sub)
      let subPrefix :
          G2nnfEqProofTree.RootToNodePath root sub :=
        state.path.trans step
      have hStep :
          AllRulesQuantifierOnPath_G2nnfEq step :=
        ⟨hRule, trivial⟩
      have hSubPrefix :
          AllRulesQuantifierOnPath_G2nnfEq subPrefix :=
        allRulesQuantifierOnPathEq_trans
          state.path step state.pathQuantifier hStep
      cases rule with
      | allSubLeft A occurrence x B t hSelected Gamma Delta =>
          simp only [G2nnfRuleCore.isQuantifierRule] at hRule
          have hPureSub :
              isPureVariableProof_G2nnfEqAux
                root sub subPrefix := by
            simpa [subPrefix, step] using
              state.pathPure.2
          have hLiveSub :
              AntecedentVariablesLive
                (closedG2nnfEqBindingEigenvariables
                  state.bindings)
                (((G2nnfRuleCore.allSubLeft
                    A occurrence x B t hSelected Gamma Delta).premises)[0]'(by omega)).1 :=
            g2nnfEqQuantifierPremise_preserves_live
              (.allSubLeft
                  A occurrence x B t hSelected Gamma Delta)
              hPrem hRule state.live
          let nextCells :=
            closedFormulaProvenanceAllSubLeft
              spec seed state.eigenMap A B occurrence x t
              hSelected Gamma state.formulaProvenance
          have hCoversSub :
              ClosedFormulaProvenanceCovers nextCells
                (((G2nnfRuleCore.allSubLeft
                    A occurrence x B t hSelected Gamma Delta).premises)[0]'(by omega)).1 :=
            closedFormulaProvenanceAllSubLeft_covers
              spec seed state.eigenMap A B occurrence x t
              hSelected Gamma state.formulaProvenance
              state.covers
          let nextState :
              ClosedG2nnfEqLowerState
                spec seed root sub :=
            { path := subPrefix
              pathQuantifier := hSubPrefix
              pathPure := hPureSub
              formulaProvenance := nextCells
              bindings := state.bindings
              trace := .allSubLeft state.trace
              covers := hCoversSub
              live := hLiveSub
              bindingEigenvariablesNodup :=
                state.bindingEigenvariablesNodup }
          have result := ih nextState hTail
          simpa [nextState, subPrefix, step,
            G2nnfEqProofTree.RootToNodePath.trans,
            g2nnfEqPath_trans_assoc] using result
      | allSubRight A occurrence x B y hSelected Gamma Delta =>
          simp only [G2nnfRuleCore.isQuantifierRule] at hRule
          have hPureSub :
              isPureVariableProof_G2nnfEqAux
                root sub subPrefix := by
            simpa [subPrefix, step] using
              state.pathPure.2
          have hLiveSub :
              AntecedentVariablesLive
                (closedG2nnfEqBindingEigenvariables
                  state.bindings)
                (((G2nnfRuleCore.allSubRight
                    A occurrence x B y hSelected Gamma Delta).premises)[0]'(by omega)).1 :=
            g2nnfEqQuantifierPremise_preserves_live
              (.allSubRight
                  A occurrence x B y hSelected Gamma Delta)
              hPrem hRule state.live
          let nextState :
              ClosedG2nnfEqLowerState
                spec seed root sub :=
            { path := subPrefix
              pathQuantifier := hSubPrefix
              pathPure := hPureSub
              formulaProvenance :=
                state.formulaProvenance
              bindings := state.bindings
              trace := .allSubRight state.trace
              covers := state.covers
              live := hLiveSub
              bindingEigenvariablesNodup :=
                state.bindingEigenvariablesNodup }
          have result := ih nextState hTail
          simpa [nextState, subPrefix, step,
            G2nnfEqProofTree.RootToNodePath.trans,
            g2nnfEqPath_trans_assoc] using result
      | exSubLeft A occurrence x B y hSelected Gamma Delta =>
          simp only [G2nnfRuleCore.isQuantifierRule] at hRule
          let exactOccurrence :
              G2nnfEqExSubLeftOccurrence root :=
            { ambient := A
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
              path := state.path }
          classical
          by_cases hRelevant : x ∈ formulaFVN B
          · have hPurityStep :=
              g2nnfEqExSubLeft_purity_step
                A B occurrence x y hSelected Gamma Delta
                hPrem hSC sub state.path state.pathPure
            have hFresh :
                y ∉
                  closedG2nnfEqBindingEigenvariables
                    state.bindings :=
              not_mem_of_g2nnfEqSequentVariableFree_of_live
                hPurityStep.1 state.live
            have hLiveSub :
                AntecedentVariablesLive
                  (closedG2nnfEqBindingEigenvariables
                    state.bindings)
                  (((G2nnfRuleCore.exSubLeft
                      A occurrence x B y hSelected Gamma Delta).premises)[0]'(by omega)).1 :=
              g2nnfEqQuantifierPremise_preserves_live
                (.exSubLeft
                    A occurrence x B y hSelected Gamma Delta)
                hPrem hRule state.live
            have hWitness :=
              g2nnfEqExSubLeft_eigenvariable_witness
                A B occurrence x y hSelected Gamma Delta
                hSC hRelevant
            let i : Fin spec.n :=
              g2nnfEqRetentiveAllocationIndex
                spec exactOccurrence state.pathQuantifier
            let hBinding :
                G2nnfEqRetentiveAllocationBinding
                  spec exactOccurrence i :=
              g2nnfEqRetentiveAllocationIndex_binding
                spec exactOccurrence state.pathQuantifier
                hRelevant
            let principals :=
              matchingClosedFormulaProvenances
                spec seed A state.formulaProvenance
            have hPrincipalExists :
                ∃ provenance,
                  provenance ∈ principals := by
              simpa [principals] using
                matchingClosedFormulaProvenances_nonempty_of_covers
                  state.covers A
                  (LCS.Finset.mem_insert.mpr (Or.inl rfl))
            have hPrincipals : principals ≠ [] := by
              intro hNil
              obtain ⟨provenance, hProvenance⟩ :=
                hPrincipalExists
              rw [hNil] at hProvenance
              simp at hProvenance
            let branch :
                (selected : {provenance //
                  provenance ∈ principals}) →
                  ClosedG2nnfEqLowerStateFamily
                    spec seed root _
                    (state.path.trans
                      (.onePremise
                        (.exSubLeft A occurrence x B y
                            hSelected Gamma Delta)
                        hAdmit hPrem hSC sub tail)) :=
              fun selected => by
                let prior := selected.1
                have hPrior :
                    prior ∈
                      matchingClosedFormulaProvenances
                        spec seed A
                          state.formulaProvenance := by
                  simpa [prior, principals] using selected.2
                have hScopeCovered :
                    prior.universalMap.Covers
                      (spec.skolemScope i) :=
                  closedFormulaProvenance_scopeCovered_g2nnfEq
                    exactOccurrence i hBinding prior
                let data :
                    ClosedG2nnfEqBindingData
                      spec seed root :=
                  makeClosedG2nnfEqBindingData
                    spec seed exactOccurrence
                    state.pathQuantifier hRelevant
                    prior hScopeCovered
                let nextCells :=
                  closedFormulaProvenanceExSubLeftRelevant
                    spec seed A B occurrence x y hSelected
                    hRelevant i prior hScopeCovered Gamma
                    state.formulaProvenance
                have hCoversSub :
                    ClosedFormulaProvenanceCovers nextCells
                      (((G2nnfRuleCore.exSubLeft
                          A occurrence x B y hSelected Gamma Delta).premises)[0]'(by omega)).1 :=
                  closedFormulaProvenanceExSubLeftRelevant_covers
                    spec seed A B occurrence x y hSelected
                    hRelevant i prior hScopeCovered Gamma
                    state.formulaProvenance state.covers
                have hLiveNext :
                    AntecedentVariablesLive
                      (closedG2nnfEqBindingEigenvariables
                        (state.bindings ++ [data]))
                      (((G2nnfRuleCore.exSubLeft
                          A occurrence x B y hSelected Gamma Delta).premises)[0]'(by omega)).1 := by
                  have hVariables :
                      closedG2nnfEqBindingEigenvariables
                          (state.bindings ++ [data]) =
                        closedG2nnfEqBindingEigenvariables
                            state.bindings ++ [y] := by
                    simp [closedG2nnfEqBindingEigenvariables,
                      data, makeClosedG2nnfEqBindingData,
                      exactOccurrence]
                  rw [hVariables]
                  exact
                    antecedentVariablesLive_append_singleton
                      hLiveSub hWitness
                have hNodup :
                    (closedG2nnfEqBindingEigenvariables
                      (state.bindings ++ [data])).Nodup := by
                  have hVariables :
                      closedG2nnfEqBindingEigenvariables
                          (state.bindings ++ [data]) =
                        closedG2nnfEqBindingEigenvariables
                            state.bindings ++ [y] := by
                    simp [closedG2nnfEqBindingEigenvariables,
                      data, makeClosedG2nnfEqBindingData,
                      exactOccurrence]
                  rw [hVariables, List.nodup_append]
                  refine
                    ⟨state.bindingEigenvariablesNodup,
                      by simp, ?_⟩
                  intro a ha b hb hab
                  have hby : b = y :=
                    List.mem_singleton.mp hb
                  subst b
                  subst a
                  exact hFresh ha
                let nextState :
                    ClosedG2nnfEqLowerState
                      spec seed root sub :=
                  { path := subPrefix
                    pathQuantifier := hSubPrefix
                    pathPure := by
                      simpa [subPrefix, step] using
                        hPurityStep.2
                    formulaProvenance := nextCells
                    bindings := state.bindings ++ [data]
                    trace :=
                      .exSubLeftRelevant state.trace
                        state.pathQuantifier hRelevant
                        prior hPrior hScopeCovered
                    covers := hCoversSub
                    live := hLiveNext
                    bindingEigenvariablesNodup := hNodup }
                have result := ih nextState hTail
                simpa [nextState, subPrefix, step,
                  G2nnfEqProofTree.RootToNodePath.trans,
                  g2nnfEqPath_trans_assoc] using result
            let families :=
              principals.attach.map branch
            have hFamilies : families ≠ [] := by
              simpa [families] using hPrincipals
            exact
              ClosedG2nnfEqLowerStateFamily.join
                families hFamilies
          · have hPureSub :
                isPureVariableProof_G2nnfEqAux
                  root sub subPrefix := by
              simpa [subPrefix, step] using
                state.pathPure.2
            have hLiveSub :
                AntecedentVariablesLive
                  (closedG2nnfEqBindingEigenvariables
                    state.bindings)
                  (((G2nnfRuleCore.exSubLeft
                      A occurrence x B y hSelected Gamma Delta).premises)[0]'(by omega)).1 :=
              g2nnfEqQuantifierPremise_preserves_live
                (.exSubLeft
                    A occurrence x B y hSelected Gamma Delta)
                hPrem hRule state.live
            let nextCells :=
              closedFormulaProvenanceExSubLeftVacuous
                spec seed A B occurrence x y hSelected
                hRelevant Gamma state.formulaProvenance
            have hCoversSub :
                ClosedFormulaProvenanceCovers nextCells
                  (((G2nnfRuleCore.exSubLeft
                      A occurrence x B y hSelected Gamma Delta).premises)[0]'(by omega)).1 :=
              closedFormulaProvenanceExSubLeftVacuous_covers
                spec seed A B occurrence x y hSelected
                hRelevant Gamma state.formulaProvenance
                state.covers
            let nextState :
                ClosedG2nnfEqLowerState
                  spec seed root sub :=
              { path := subPrefix
                pathQuantifier := hSubPrefix
                pathPure := hPureSub
                formulaProvenance := nextCells
                bindings := state.bindings
                trace :=
                  .exSubLeftVacuous state.trace hRelevant
                covers := hCoversSub
                live := hLiveSub
                bindingEigenvariablesNodup :=
                  state.bindingEigenvariablesNodup }
            have result := ih nextState hTail
            simpa [nextState, subPrefix, step,
              G2nnfEqProofTree.RootToNodePath.trans,
              g2nnfEqPath_trans_assoc] using result
      | exSubRight A occurrence x B t hSelected Gamma Delta =>
          simp only [G2nnfRuleCore.isQuantifierRule] at hRule
          have hPureSub :
              isPureVariableProof_G2nnfEqAux
                root sub subPrefix := by
            simpa [subPrefix, step] using
              state.pathPure.2
          have hLiveSub :
              AntecedentVariablesLive
                (closedG2nnfEqBindingEigenvariables
                  state.bindings)
                (((G2nnfRuleCore.exSubRight
                    A occurrence x B t hSelected Gamma Delta).premises)[0]'(by omega)).1 :=
            g2nnfEqQuantifierPremise_preserves_live
              (.exSubRight
                  A occurrence x B t hSelected Gamma Delta)
              hPrem hRule state.live
          let nextState :
              ClosedG2nnfEqLowerState
                spec seed root sub :=
            { path := subPrefix
              pathQuantifier := hSubPrefix
              pathPure := hPureSub
              formulaProvenance :=
                state.formulaProvenance
              bindings := state.bindings
              trace := .exSubRight state.trace
              covers := state.covers
              live := hLiveSub
              bindingEigenvariablesNodup :=
                state.bindingEigenvariablesNodup }
          have result := ih nextState hTail
          simpa [nextState, subPrefix, step,
            G2nnfEqProofTree.RootToNodePath.trans,
            g2nnfEqPath_trans_assoc] using result
      | _ =>
          simp_all [G2nnfRuleCore.isQuantifierRule]
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

end LCS.Herbrand.SHGTheorem.Herbrand
end

