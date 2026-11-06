import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.Herbrand.NNFHauptsatz.Equality
import LCS.Herbrand.SHGTheorem.Herbrand.ExistentialOccurrences

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

structure FormulaOccurrenceFocus (L : Language) where
  ambient : FormulaN L
  address : FormulaOccurrenceAddress

inductive G2nnfPremiseChoice : Type where
  | only
  | left
  | right
  deriving DecidableEq

/-- Replay a root-to-node sequence of quantifier substitutions in
root-to-node order on a formula. `formulaSubstN` masks a substitution
under a quantifier binding the same variable. -/
def replayQuantifierSubstitutionsFormula {L : Language} :
    List (Nat × Term L) → FormulaN L → FormulaN L
  | [], A => A
  | (x, replacement) :: rest, A =>
    replayQuantifierSubstitutionsFormula rest
      (formulaSubstN A replacement x)

/-- One exact `∃:left` Core inference in a fixed equality-free G2nnf
proof tree. The stored contexts, selected maximal occurrence and NNF side
conditions determine the inference; its Type-valued root-to-node path
records every premise choice, even for equal subtree values. -/
structure G2nnfExSubLeftOccurrence {L : Language}
    {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    (root : G2nnfProofTree hL Γroot Δroot) : Type where
  ambient : FormulaN L
  maxOccurrence : MaxQuantifierOccurrence ambient
  boundVar : Nat
  body : FormulaN L
  eigenvariable : Nat
  hSelected :
    maxOccurrence.selected = FormulaN.ex boundVar body
  gamma : LCS.Finset (FormulaN L)
  delta : LCS.Finset (FormulaN L)
  hPrem :
    (G2nnfRuleCore.exSubLeft ambient maxOccurrence boundVar body
      eigenvariable hSelected gamma delta).premises.length = 1
  hSC :
    G2nnfRuleCore.SideConditions
      (.exSubLeft ambient maxOccurrence boundVar body
        eigenvariable hSelected gamma delta)
  premise : G2nnfProofTree hL
    ((G2nnfRuleCore.exSubLeft ambient maxOccurrence boundVar body
      eigenvariable hSelected gamma delta).premises[0]'(by omega)).1
    ((G2nnfRuleCore.exSubLeft ambient maxOccurrence boundVar body
      eigenvariable hSelected gamma delta).premises[0]'(by omega)).2
  path : G2nnfProofTree.RootToNodePath root
    (.onePremise
      (.exSubLeft ambient maxOccurrence boundVar body
        eigenvariable hSelected gamma delta)
      (by trivial) hPrem hSC premise)

/-- Equality-system mirror of `G2nnfExSubLeftOccurrence`. Its target is
exactly an existential-left Core inference, with the stored contexts and
NNF side conditions. Equality axioms are leaves and cannot inhabit this
inference package. -/
structure G2nnfEqExSubLeftOccurrence {L : Language}
    {hL : L.hasEquality = true} [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    (root : G2nnfEqProofTree hL Γroot Δroot) : Type where
  ambient : FormulaN L
  maxOccurrence : MaxQuantifierOccurrence ambient
  boundVar : Nat
  body : FormulaN L
  eigenvariable : Nat
  hSelected :
    maxOccurrence.selected = FormulaN.ex boundVar body
  gamma : LCS.Finset (FormulaN L)
  delta : LCS.Finset (FormulaN L)
  hPrem :
    (G2nnfRuleCore.exSubLeft ambient maxOccurrence boundVar body
      eigenvariable hSelected gamma delta).premises.length = 1
  hSC :
    G2nnfRuleCore.SideConditions
      (.exSubLeft ambient maxOccurrence boundVar body
        eigenvariable hSelected gamma delta)
  premise : G2nnfEqProofTree hL
    ((G2nnfRuleCore.exSubLeft ambient maxOccurrence boundVar body
      eigenvariable hSelected gamma delta).premises[0]'(by omega)).1
    ((G2nnfRuleCore.exSubLeft ambient maxOccurrence boundVar body
      eigenvariable hSelected gamma delta).premises[0]'(by omega)).2
  path : G2nnfEqProofTree.RootToNodePath root
    (.onePremise
      (.exSubLeft ambient maxOccurrence boundVar body
        eigenvariable hSelected gamma delta)
      (by trivial) hPrem hSC premise)

/-- Data of one relevant existential-left step.  Relevance means that
the eliminated binder genuinely occurs free in its body; vacuous
existential steps are deliberately absent from the chronological
eigenvariable map. -/
structure RelevantExSubLeftStep (L : Language) where
  ambient : FormulaN L
  maxOccurrence : MaxQuantifierOccurrence ambient
  boundVar : Nat
  body : FormulaN L
  eigenvariable : Nat
  hSelected :
    maxOccurrence.selected = FormulaN.ex boundVar body
  hRelevant : boundVar ∈ formulaFVN body

/-- Collision-tolerant whole-formula antecedent lineage.  At a left
quantifier step the exact constructor-carried occurrence supplies the
principal branch, while any formula in the raw context may also be
retained.  Those branches are intentionally not made exclusive:
`Finset` insertion can make principal and context formulae collide. -/
def g2nnfRetentiveAntecedentLineage {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot}
    {node : G2nnfProofTree hL Γnode Δnode} :
    (path : G2nnfProofTree.RootToNodePath root node) →
    FormulaN L → FormulaN L → Prop
  | .root _, source, target =>
      source = target
  | .onePremise rule _ _ _ _ path,
      source, target =>
      match rule with
      | .allSubLeft A occurrence x B t _ Gamma Delta =>
          (source = A ∧
            g2nnfRetentiveAntecedentLineage path
              (occurrence.replace (formulaSubstN B t x))
              target) ∨
          (source ∈ Gamma ∧
            g2nnfRetentiveAntecedentLineage path
              source target)
      | .exSubLeft A occurrence x B y _ Gamma Delta =>
          (source = A ∧
            g2nnfRetentiveAntecedentLineage path
              (occurrence.replace
                (formulaSubstN B (.var y) x))
              target) ∨
          (source ∈ Gamma ∧
            g2nnfRetentiveAntecedentLineage path
              source target)
      | .allSubRight _ _ _ _ _ _ Gamma Delta =>
          source ∈ Gamma ∧
            g2nnfRetentiveAntecedentLineage path
              source target
      | .exSubRight _ _ _ _ _ _ Gamma Delta =>
          source ∈ Gamma ∧
            g2nnfRetentiveAntecedentLineage path
              source target
      | _ => False
  | .leftPremise _ _ _ _ _ _ _, _, _ => False
  | .rightPremise _ _ _ _ _ _ _, _, _ => False

/-- Equality-system mirror of retentive antecedent lineage. -/
noncomputable def g2nnfEqRetentiveAntecedentLineage
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL Γroot Δroot}
    {node : G2nnfEqProofTree hL Γnode Δnode} :
    (path : G2nnfEqProofTree.RootToNodePath root node) →
    FormulaN L → FormulaN L → Prop
  | .root _, source, target =>
      source = target
  | .onePremise rule _ _ _ _ path,
      source, target =>
      match rule with
      | .allSubLeft A occurrence x B t _ Gamma Delta =>
          (source = A ∧
            g2nnfEqRetentiveAntecedentLineage path
              (occurrence.replace (formulaSubstN B t x))
              target) ∨
          (source ∈ Gamma ∧
            g2nnfEqRetentiveAntecedentLineage path
              source target)
      | .exSubLeft A occurrence x B y _ Gamma Delta =>
          (source = A ∧
            g2nnfEqRetentiveAntecedentLineage path
              (occurrence.replace
                (formulaSubstN B (.var y) x))
              target) ∨
          (source ∈ Gamma ∧
            g2nnfEqRetentiveAntecedentLineage path
              source target)
      | .allSubRight _ _ _ _ _ _ Gamma Delta =>
          source ∈ Gamma ∧
            g2nnfEqRetentiveAntecedentLineage path
              source target
      | .exSubRight _ _ _ _ _ _ Gamma Delta =>
          source ∈ Gamma ∧
            g2nnfEqRetentiveAntecedentLineage path
              source target
      | _ => False
  | .leftPremise _ _ _ _ _ _ _, _, _ => False
  | .rightPremise _ _ _ _ _ _ _, _, _ => False

/-- Every endpoint antecedent formula on a quantifier-only path has
a retentive lineage from some formula in the root antecedent. -/
theorem g2nnfRetentiveAntecedentLineage_of_mem
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot}
    {node : G2nnfProofTree hL Γnode Δnode}
    (path : G2nnfProofTree.RootToNodePath root node)
    (hQuantifier : AllRulesQuantifierOnPath path)
    {target : FormulaN L} (hTarget : target ∈ Γnode) :
    ∃ source ∈ Γroot,
      g2nnfRetentiveAntecedentLineage
        path source target := by
  induction path with
  | root T =>
      exact ⟨target, hTarget, rfl⟩
  | onePremise rule hAdmit hPrem hSC sub path ih =>
      rcases hQuantifier with ⟨hRule, hPath⟩
      cases rule <;>
        simp only [G2nnfRuleCore.isQuantifierRule] at hRule
      next A occurrence x B t hSelected Gamma Delta =>
        obtain ⟨source, hSource, hLineage⟩ :=
          ih hPath hTarget
        change source ∈ LCS.Finset.insert
          (occurrence.replace (formulaSubstN B t x))
          Gamma at hSource
        rw [LCS.Finset.mem_insert] at hSource
        rcases hSource with rfl | hContext
        · refine
            ⟨A, LCS.Finset.mem_insert.mpr (Or.inl rfl), ?_⟩
          exact Or.inl ⟨rfl, hLineage⟩
        · refine
            ⟨source,
              LCS.Finset.mem_insert.mpr (Or.inr hContext), ?_⟩
          exact Or.inr ⟨hContext, hLineage⟩
      next A occurrence x B y hSelected Gamma Delta =>
        obtain ⟨source, hSource, hLineage⟩ :=
          ih hPath hTarget
        exact ⟨source, hSource, hSource, hLineage⟩
      next A occurrence x B y hSelected Gamma Delta =>
        obtain ⟨source, hSource, hLineage⟩ :=
          ih hPath hTarget
        change source ∈ LCS.Finset.insert
          (occurrence.replace
            (formulaSubstN B (.var y) x))
          Gamma at hSource
        rw [LCS.Finset.mem_insert] at hSource
        rcases hSource with rfl | hContext
        · refine
            ⟨A, LCS.Finset.mem_insert.mpr (Or.inl rfl), ?_⟩
          exact Or.inl ⟨rfl, hLineage⟩
        · refine
            ⟨source,
              LCS.Finset.mem_insert.mpr (Or.inr hContext), ?_⟩
          exact Or.inr ⟨hContext, hLineage⟩
      next A occurrence x B t hSelected Gamma Delta =>
        obtain ⟨source, hSource, hLineage⟩ :=
          ih hPath hTarget
        exact ⟨source, hSource, hSource, hLineage⟩
  | leftPremise rule hAdmit hPrem hSC sub₁ sub₂ path ih =>
      rcases hQuantifier with ⟨hRule, _⟩
      cases rule <;>
        simp [G2nnfRuleCore.isQuantifierRule,
          G2nnfRuleCore.premises] at hRule hPrem
  | rightPremise rule hAdmit hPrem hSC sub₁ sub₂ path ih =>
      rcases hQuantifier with ⟨hRule, _⟩
      cases rule <;>
        simp [G2nnfRuleCore.isQuantifierRule,
          G2nnfRuleCore.premises] at hRule hPrem

/-- Singleton-root specialization of retentive coverage. -/
theorem g2nnfRetentiveAntecedentLineage_from_singleton
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {source : FormulaN L}
    {Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL
      ({source} : LCS.Finset (FormulaN L)) Δroot}
    {node : G2nnfProofTree hL Γnode Δnode}
    (path : G2nnfProofTree.RootToNodePath root node)
    (hQuantifier : AllRulesQuantifierOnPath path)
    {target : FormulaN L} (hTarget : target ∈ Γnode) :
    g2nnfRetentiveAntecedentLineage
      path source target := by
  obtain ⟨rootSource, hRootSource, hLineage⟩ :=
    g2nnfRetentiveAntecedentLineage_of_mem
      path hQuantifier hTarget
  have hEq : rootSource = source :=
    (LCS.Finset.mem_singleton rootSource source).mp
      hRootSource
  subst rootSource
  exact hLineage

/-- Equality-system retentive coverage along a quantifier-only exact
path. -/
theorem g2nnfEqRetentiveAntecedentLineage_of_mem
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL Γroot Δroot}
    {node : G2nnfEqProofTree hL Γnode Δnode}
    (path : G2nnfEqProofTree.RootToNodePath root node)
    (hQuantifier :
      AllRulesQuantifierOnPath_G2nnfEq path)
    {target : FormulaN L} (hTarget : target ∈ Γnode) :
    ∃ source ∈ Γroot,
      g2nnfEqRetentiveAntecedentLineage
        path source target := by
  induction path with
  | root T =>
      exact ⟨target, hTarget, rfl⟩
  | onePremise rule hAdmit hPrem hSC sub path ih =>
      rcases hQuantifier with ⟨hRule, hPath⟩
      cases rule <;>
        simp only [G2nnfRuleCore.isQuantifierRule] at hRule
      next A occurrence x B t hSelected Gamma Delta =>
        obtain ⟨source, hSource, hLineage⟩ :=
          ih hPath hTarget
        change source ∈ LCS.Finset.insert
          (occurrence.replace (formulaSubstN B t x))
          Gamma at hSource
        rw [LCS.Finset.mem_insert] at hSource
        rcases hSource with rfl | hContext
        · refine
            ⟨A, LCS.Finset.mem_insert.mpr (Or.inl rfl), ?_⟩
          exact Or.inl ⟨rfl, hLineage⟩
        · refine
            ⟨source,
              LCS.Finset.mem_insert.mpr (Or.inr hContext), ?_⟩
          exact Or.inr ⟨hContext, hLineage⟩
      next A occurrence x B y hSelected Gamma Delta =>
        obtain ⟨source, hSource, hLineage⟩ :=
          ih hPath hTarget
        exact ⟨source, hSource, hSource, hLineage⟩
      next A occurrence x B y hSelected Gamma Delta =>
        obtain ⟨source, hSource, hLineage⟩ :=
          ih hPath hTarget
        change source ∈ LCS.Finset.insert
          (occurrence.replace
            (formulaSubstN B (.var y) x))
          Gamma at hSource
        rw [LCS.Finset.mem_insert] at hSource
        rcases hSource with rfl | hContext
        · refine
            ⟨A, LCS.Finset.mem_insert.mpr (Or.inl rfl), ?_⟩
          exact Or.inl ⟨rfl, hLineage⟩
        · refine
            ⟨source,
              LCS.Finset.mem_insert.mpr (Or.inr hContext), ?_⟩
          exact Or.inr ⟨hContext, hLineage⟩
      next A occurrence x B t hSelected Gamma Delta =>
        obtain ⟨source, hSource, hLineage⟩ :=
          ih hPath hTarget
        exact ⟨source, hSource, hSource, hLineage⟩
  | leftPremise rule hAdmit hPrem hSC sub₁ sub₂ path ih =>
      rcases hQuantifier with ⟨hRule, _⟩
      cases rule <;>
        simp [G2nnfRuleCore.isQuantifierRule,
          G2nnfRuleCore.premises] at hRule hPrem
  | rightPremise rule hAdmit hPrem hSC sub₁ sub₂ path ih =>
      rcases hQuantifier with ⟨hRule, _⟩
      cases rule <;>
        simp [G2nnfRuleCore.isQuantifierRule,
          G2nnfRuleCore.premises] at hRule hPrem

/-- Singleton-root equality specialization of retentive coverage. -/
theorem g2nnfEqRetentiveAntecedentLineage_from_singleton
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {source : FormulaN L}
    {Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL
      ({source} : LCS.Finset (FormulaN L)) Δroot}
    {node : G2nnfEqProofTree hL Γnode Δnode}
    (path : G2nnfEqProofTree.RootToNodePath root node)
    (hQuantifier :
      AllRulesQuantifierOnPath_G2nnfEq path)
    {target : FormulaN L} (hTarget : target ∈ Γnode) :
    g2nnfEqRetentiveAntecedentLineage
      path source target := by
  obtain ⟨rootSource, hRootSource, hLineage⟩ :=
    g2nnfEqRetentiveAntecedentLineage_of_mem
      path hQuantifier hTarget
  have hEq : rootSource = source :=
    (LCS.Finset.mem_singleton rootSource source).mp
      hRootSource
  subst rootSource
  exact hLineage

/-- A retentive G2nnf lineage cannot introduce a new existential binder.
Principal quantifier steps remove one selected quantifier and substitute
inside its body; retained-context branches leave the formula unchanged. -/
theorem g2nnfRetentiveAntecedentLineage_exBinders
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot}
    {node : G2nnfProofTree hL Γnode Δnode}
    {path : G2nnfProofTree.RootToNodePath root node}
    {source target : FormulaN L}
    (hLineage :
      g2nnfRetentiveAntecedentLineage path source target) :
    ∀ x, x ∈ existentialBinderSequence target →
      x ∈ existentialBinderSequence source := by
  induction path generalizing source target with
  | root T =>
      simp only [g2nnfRetentiveAntecedentLineage] at hLineage
      subst target
      intro x hx
      exact hx
  | onePremise rule hAdmit hPrem hSC sub path ih =>
      cases rule <;>
        simp only [g2nnfRetentiveAntecedentLineage] at hLineage
      next A occurrence x B t hSelected Gamma Delta =>
        rcases hLineage with
          ⟨rfl, hTail⟩ | ⟨hContext, hTail⟩
        · intro y hy
          exact
            maxQuantifierOccurrence_replace_allSub_exBinders
              occurrence x t hSelected y (ih hTail y hy)
        · exact ih hTail
      next A occurrence x B y hSelected Gamma Delta =>
        exact ih hLineage.2
      next A occurrence x B y hSelected Gamma Delta =>
        rcases hLineage with
          ⟨rfl, hTail⟩ | ⟨hContext, hTail⟩
        · intro z hz
          exact
            maxQuantifierOccurrence_replace_exSub_exBinders
              occurrence x (.var y) hSelected z
              (ih hTail z hz)
        · exact ih hTail
      next A occurrence x B t hSelected Gamma Delta =>
        exact ih hLineage.2
  | leftPremise rule hAdmit hPrem hSC sub₁ sub₂ path ih =>
      exact hLineage.elim
  | rightPremise rule hAdmit hPrem hSC sub₁ sub₂ path ih =>
      exact hLineage.elim

/-- Equality-system mirror of existential-binder preservation along a
retentive lower lineage. -/
theorem g2nnfEqRetentiveAntecedentLineage_exBinders
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL Γroot Δroot}
    {node : G2nnfEqProofTree hL Γnode Δnode}
    {path : G2nnfEqProofTree.RootToNodePath root node}
    {source target : FormulaN L}
    (hLineage :
      g2nnfEqRetentiveAntecedentLineage
        path source target) :
    ∀ x, x ∈ existentialBinderSequence target →
      x ∈ existentialBinderSequence source := by
  induction path generalizing source target with
  | root T =>
      simp only [g2nnfEqRetentiveAntecedentLineage] at hLineage
      subst target
      intro x hx
      exact hx
  | onePremise rule hAdmit hPrem hSC sub path ih =>
      cases rule <;>
        simp only [g2nnfEqRetentiveAntecedentLineage] at hLineage
      next A occurrence x B t hSelected Gamma Delta =>
        rcases hLineage with
          ⟨rfl, hTail⟩ | ⟨hContext, hTail⟩
        · intro y hy
          exact
            maxQuantifierOccurrence_replace_allSub_exBinders
              occurrence x t hSelected y (ih hTail y hy)
        · exact ih hTail
      next A occurrence x B y hSelected Gamma Delta =>
        exact ih hLineage.2
      next A occurrence x B y hSelected Gamma Delta =>
        rcases hLineage with
          ⟨rfl, hTail⟩ | ⟨hContext, hTail⟩
        · intro z hz
          exact
            maxQuantifierOccurrence_replace_exSub_exBinders
              occurrence x (.var y) hSelected z
              (ih hTail z hz)
        · exact ih hTail
      next A occurrence x B t hSelected Gamma Delta =>
        exact ih hLineage.2
  | leftPremise rule hAdmit hPrem hSC sub₁ sub₂ path ih =>
      exact hLineage.elim
  | rightPremise rule hAdmit hPrem hSC sub₁ sub₂ path ih =>
      exact hLineage.elim

end LCS.Herbrand.SHGTheorem.Herbrand
end
