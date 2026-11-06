import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.Herbrand.NNFHauptsatz.Equality
import LCS.Herbrand.SHGTheorem.Herbrand.SkolemNormalForm
import LCS.Herbrand.SHGTheorem.Herbrand.OccurrenceLineage

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

-- retained: used by LCS.FOResolution.Method.HerbrandBridge
/-- Retention-aware antecedent lineage along an exact root-to-node path
consisting of universal-left steps. Unlike strict occurrence lineage, this
relation follows either the transformed principal formula or a retained
`Finset` context cell, including the case where their formulae collide. -/
def g2nnfUniversalAntecedentLineage {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hNoEq Γroot Δroot}
    {node : G2nnfProofTree hNoEq Γnode Δnode} :
    (path : G2nnfProofTree.RootToNodePath root node) →
    FormulaN L → FormulaN L → List (Nat × Term L) → Prop
  | .root _, source, target, substitutions =>
      source = target ∧ substitutions = []
  | .onePremise rule _ _ _ _ path,
      source, target, substitutions =>
      match rule with
      | .allSubLeft A occurrence x B t _ Gamma _ =>
          (source ∈ Gamma ∧
            g2nnfUniversalAntecedentLineage path
              source target substitutions) ∨
          ∃ tail,
            source = A ∧
            g2nnfUniversalAntecedentLineage path
              (occurrence.replace (formulaSubstN B t x))
              target tail ∧
            substitutions = (x, t) :: tail
      | _ => False
  | .leftPremise _ _ _ _ _ _ _, _, _, _ => False
  | .rightPremise _ _ _ _ _ _ _, _, _, _ => False

-- retained: used by LCS.Herbrand.SHGTheorem.Main.GroundMatrix, LCS.Herbrand.SHGTheorem.Main.SHG
/-- Substitution commutes with extraction of a prenex matrix when the
substituted variable is not bound in the formula. -/
theorem prenexMatrix_formulaSubstN_of_not_bv {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat)
    (h : ¬x ∈ formulaBVN A) :
    prenexMatrix (formulaSubstN A t x) =
      formulaSubstN (prenexMatrix A) t x := by
  induction A with
  | predN P ts => rfl
  | eq_ hEq t₁ t₂ => rfl
  | neg A ih => rfl
  | conj A B ihA ihB => rfl
  | disj A B ihA ihB => rfl
  | impl A B ihA ihB => rfl
  | all y A ih =>
      have hxy : x ≠ y := by
        intro hEq
        apply h
        simp [hEq, formulaBVN]
      have hA : ¬x ∈ formulaBVN A := by
        intro hx
        apply h
        simp [formulaBVN, hx]
      simp [formulaSubstN, hxy, prenexMatrix, ih hA]
  | ex y A ih =>
      have hxy : x ≠ y := by
        intro hEq
        apply h
        simp [hEq, formulaBVN]
      have hA : ¬x ∈ formulaBVN A := by
        intro hx
        apply h
        simp [formulaBVN, hx]
      simp [formulaSubstN, hxy, prenexMatrix, ih hA]

-- retained: used by LCS.Herbrand.SHGTheorem.Main.SHG
theorem isQuantifierFree_prenexPrefix_eq_nil {L : Language}
    (A : FormulaN L) (h : isQuantifierFree A) :
    prenexPrefix A = [] := by
  cases A <;> simp_all [isQuantifierFree, prenexPrefix]

-- retained: used by LCS.Herbrand.SHGTheorem.Main.GroundMatrix
theorem isQuantifierFree_prenexMatrix_eq_self {L : Language}
    (A : FormulaN L) (h : isQuantifierFree A) :
    prenexMatrix A = A := by
  cases A <;> simp_all [isQuantifierFree, prenexMatrix]

-- retained: used by LCS.FOResolution.Method.HerbrandBridge
/-- A universal-prenex lineage reaching a quantifier-free target consumes
the complete source prefix, in order, and replays to that exact target. -/
theorem g2nnfUniversalAntecedentLineage_fullPrefixReplay
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hNoEq Γroot Δroot}
    {node : G2nnfProofTree hNoEq Γnode Δnode}
    {path : G2nnfProofTree.RootToNodePath root node}
    {source target : FormulaN L}
    {substitutions : List (Nat × Term L)}
    (hLineage : g2nnfUniversalAntecedentLineage path
      source target substitutions)
    (hPrenex : isPrenex source)
    (hUniversal : ∀ p ∈ prenexPrefix source,
      p.1 = QuantifierKind.universal)
    (hDistinct : distinctQuantifierBindings source)
    (hTargetQf : isQuantifierFree target) :
    substitutions.map Prod.fst =
        (prenexPrefix source).map Prod.snd ∧
      replayQuantifierSubstitutionsFormula substitutions
        (prenexMatrix source) = target := by
  induction path generalizing source substitutions with
  | root T =>
      simp only [g2nnfUniversalAntecedentLineage] at hLineage
      rcases hLineage with ⟨rfl, rfl⟩
      constructor
      · simpa using isQuantifierFree_prenexPrefix_eq_nil _ hTargetQf
      · change prenexMatrix source = source
        exact isQuantifierFree_prenexMatrix_eq_self _ hTargetQf
  | onePremise rule hAdmit hPrem hSC sub path ih =>
      cases rule <;>
        simp only [g2nnfUniversalAntecedentLineage] at hLineage
      next A occurrence x B t hSelected Gamma Delta =>
        rcases hLineage with hContext | hPrincipal
        · exact ih hContext.2 hPrenex hUniversal hDistinct
        · rcases hPrincipal with ⟨tail, rfl, hTail, rfl⟩
          have hShape :
              source = FormulaN.all x B :=
            (eq_of_mem_maxQuantSubformulae_of_isPrenex
              source occurrence.selected hPrenex
              occurrence.selected_mem).symm.trans hSelected
          subst source
          cases occurrence
          simp only [MaxQuantifierOccurrence.replace] at hTail
          have hPrenexB : isPrenex B := hPrenex
          have hUniversalB :
              ∀ p ∈ prenexPrefix B,
                p.1 = QuantifierKind.universal := by
            intro p hp
            apply hUniversal p
            simp [prenexPrefix, hp]
          have hPrenexSub :
              isPrenex (formulaSubstN B t x) :=
            isPrenex_formulaSubstN B t x hPrenexB
          have hUniversalSub :
              ∀ p ∈ prenexPrefix (formulaSubstN B t x),
                p.1 = QuantifierKind.universal := by
            intro p hp
            apply hUniversalB p
            rwa [prenexPrefix_formulaSubstN] at hp
          have hDistinctSub :
              distinctQuantifierBindings
                (formulaSubstN B t x) :=
            distinctQuantifierBindings_of_formulaSubstN
              B t x hDistinct.1
          obtain ⟨hPrefix, hReplay⟩ :=
            ih hTail hPrenexSub hUniversalSub
              hDistinctSub
          constructor
          · simp [prenexPrefix, prenexPrefix_formulaSubstN,
              hPrefix]
          · simp only [replayQuantifierSubstitutionsFormula,
              prenexMatrix]
            rw [← prenexMatrix_formulaSubstN_of_not_bv
              B t x hDistinct.2]
            exact hReplay
  | leftPremise rule hAdmit hPrem hSC sub1 sub2 path ih =>
      exact hLineage.elim
  | rightPremise rule hAdmit hPrem hSC sub1 sub2 path ih =>
      exact hLineage.elim

-- retained: used by LCS.FOResolution.Method.HerbrandBridge
/-- Every formula in the endpoint antecedent of an all-left path has a
retention-aware lineage from some formula in the root antecedent. -/
theorem g2nnfUniversalAntecedentLineage_of_mem
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hNoEq Γroot Δroot}
    {node : G2nnfProofTree hNoEq Γnode Δnode}
    (path : G2nnfProofTree.RootToNodePath root node)
    (hAll : AllRulesAllSubLeftOnPath path)
    {target : FormulaN L} (hTarget : target ∈ Γnode) :
    ∃ source ∈ Γroot, ∃ substitutions,
      g2nnfUniversalAntecedentLineage path
        source target substitutions := by
  induction path with
  | root T =>
      exact ⟨target, hTarget, [], rfl, rfl⟩
  | onePremise rule hAdmit hPrem hSC sub path ih =>
      cases rule <;>
        simp only [AllRulesAllSubLeftOnPath] at hAll
      case allSubLeft A occurrence x B t hSelected Gamma Delta =>
        obtain ⟨source, hSource, substitutions, hLineage⟩ :=
          ih hAll hTarget
        change source ∈ LCS.Finset.insert
          (occurrence.replace (formulaSubstN B t x))
          Gamma at hSource
        rw [LCS.Finset.mem_insert] at hSource
        rcases hSource with hInserted | hContext
        · refine ⟨A, LCS.Finset.mem_insert.mpr (Or.inl rfl),
            (x, t) :: substitutions, ?_⟩
          right
          exact ⟨substitutions, rfl, hInserted ▸ hLineage, rfl⟩
        · refine ⟨source,
            LCS.Finset.mem_insert.mpr (Or.inr hContext),
            substitutions, ?_⟩
          left
          exact ⟨hContext, hLineage⟩
  | leftPremise rule hAdmit hPrem hSC sub1 sub2 path ih =>
      exact hAll.elim
  | rightPremise rule hAdmit hPrem hSC sub1 sub2 path ih =>
      exact hAll.elim

-- retained: used by LCS.FOResolution.Method.HerbrandBridge
/-- Singleton specialization of antecedent-lineage coverage. -/
theorem g2nnfUniversalAntecedentLineage_from_singleton
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {B : FormulaN L} {Δroot Γnode Δnode :
      LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hNoEq
      ({B} : LCS.Finset (FormulaN L)) Δroot}
    {node : G2nnfProofTree hNoEq Γnode Δnode}
    (path : G2nnfProofTree.RootToNodePath root node)
    (hAll : AllRulesAllSubLeftOnPath path)
    {target : FormulaN L} (hTarget : target ∈ Γnode) :
    ∃ substitutions,
      g2nnfUniversalAntecedentLineage path
        B target substitutions := by
  obtain ⟨source, hSource, substitutions, hLineage⟩ :=
    g2nnfUniversalAntecedentLineage_of_mem
      path hAll hTarget
  have hEq : source = B :=
    (LCS.Finset.mem_singleton source B).mp hSource
  subst source
  exact ⟨substitutions, hLineage⟩

-- retained: used by LCS.FOResolution.Method.HerbrandBridge
/-- Full-prefix specialization at the same occurrence supplied by the
midsequent theorem. -/
theorem universalPrenexSingleton_midsequentFullPrefix
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (source : FormulaN L)
    (hSource : UniversalPrenexFormula source)
    (hDistinct : distinctQuantifierBindings source)
    {T : G2nnfProofTree hNoEq
      (LCS.Finset.singleton source) LCS.Finset.empty}
    (mid : LCS.Finset (FormulaN L) ×
      LCS.Finset (FormulaN L))
    (hMid : IsMidsequentG2nnf T mid) :
    mid.2 = LCS.Finset.empty ∧
    ∃ occurrence : G2nnfProofTree.NodeOccurrence T mid.1 mid.2,
      AllRulesPropOrWeakening occurrence.node ∧
      AllRulesAllSubLeftOnPath occurrence.path ∧
      ∀ target, target ∈ mid.1 →
        ∃ substitutions,
          g2nnfUniversalAntecedentLineage occurrence.path
              source target substitutions ∧
            substitutions.map Prod.fst =
              (prenexPrefix source).map Prod.snd ∧
            replayQuantifierSubstitutionsFormula substitutions
              (prenexMatrix source) = target := by
  rcases universalPrenexSingleton_midsequentSpecialization
      source hSource mid hMid with
    ⟨hSuccedent, occurrence, hAbove, hAllSubLeft,
      hAntecedent⟩
  refine ⟨hSuccedent, occurrence, hAbove, hAllSubLeft, ?_⟩
  intro target hTarget
  obtain ⟨substitutions, hLineage⟩ :=
    g2nnfUniversalAntecedentLineage_from_singleton
      occurrence.path hAllSubLeft hTarget
  obtain ⟨hPrefix, hReplay⟩ :=
    g2nnfUniversalAntecedentLineage_fullPrefixReplay
      hLineage hSource.1 hSource.2 hDistinct
      (hMid.midIsQuantifierFree.1 target hTarget)
  exact ⟨substitutions, hLineage, hPrefix, hReplay⟩

-- retained: used by LCS.FOResolution.Method.HerbrandBridge
/-- Universal-left steps preserve nonemptiness of the antecedent. -/
theorem antecedent_ne_empty_of_allSubLeftOnPath
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hNoEq Γroot Δroot}
    {node : G2nnfProofTree hNoEq Γnode Δnode}
    (path : G2nnfProofTree.RootToNodePath root node)
    (hAll : AllRulesAllSubLeftOnPath path)
    (hRoot : Γroot ≠ LCS.Finset.empty) :
    Γnode ≠ LCS.Finset.empty := by
  induction path with
  | root T =>
      exact hRoot
  | onePremise rule hAdmit hPrem hSC sub path ih =>
      cases rule <;>
        simp only [AllRulesAllSubLeftOnPath] at hAll
      case allSubLeft A occurrence x B t hSelected Gamma Delta =>
        apply ih hAll
        intro hEmpty
        change LCS.Finset.insert
          (occurrence.replace (formulaSubstN B t x))
          Gamma = LCS.Finset.empty at hEmpty
        have hInserted :
            occurrence.replace (formulaSubstN B t x) ∈
              LCS.Finset.insert
                (occurrence.replace (formulaSubstN B t x))
                Gamma :=
          LCS.Finset.mem_insert.mpr (Or.inl rfl)
        rw [hEmpty] at hInserted
        exact LCS.Finset.not_mem_empty hInserted
  | leftPremise rule hAdmit hPrem hSC sub1 sub2 path ih =>
      exact hAll.elim
  | rightPremise rule hAdmit hPrem hSC sub1 sub2 path ih =>
      exact hAll.elim

-- retained: used by LCS.FOResolution.Method.HerbrandBridge
theorem finset_ofList_toList {α : Type} [DecidableEq α]
    (S : LCS.Finset α) :
    LCS.Finset.ofList S.toList = S := by
  apply LCS.Finset.ext
  intro a
  rw [LCS.Finset.mem_ofList, LCS.Finset.mem_toList]

-- retained: used by LCS.FOResolution.Method.HerbrandBridge
theorem finset_toList_ne_nil_of_ne_empty
    {α : Type} [DecidableEq α]
    (S : LCS.Finset α)
    (hS : S ≠ LCS.Finset.empty) :
    S.toList ≠ [] := by
  intro hNil
  apply hS
  apply LCS.Finset.ext
  intro a
  constructor
  · intro ha
    have hList : a ∈ S.toList :=
      (LCS.Finset.mem_toList S a).mpr ha
    rw [hNil] at hList
    simp at hList
  · intro ha
    exact (LCS.Finset.not_mem_empty ha).elim

-- retained: used by LCS.FOResolution.Method.HerbrandBridge
/-- Enumerate the actual midsequent antecedent list, preserving the same
node occurrence and giving full-prefix lineage for every list cell. -/
theorem universalPrenexSingleton_midsequentFullPrefixList
    {L : Language} {hNoEq : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    (source : FormulaN L)
    (hSource : UniversalPrenexFormula source)
    (hDistinct : distinctQuantifierBindings source)
    {T : G2nnfProofTree hNoEq
      (LCS.Finset.singleton source) LCS.Finset.empty}
    (mid : LCS.Finset (FormulaN L) ×
      LCS.Finset (FormulaN L))
    (hMid : IsMidsequentG2nnf T mid) :
    mid.2 = LCS.Finset.empty ∧
    ∃ (occurrence : G2nnfProofTree.NodeOccurrence
          T mid.1 mid.2)
        (instances : List (FormulaN L)),
      AllRulesPropOrWeakening occurrence.node ∧
      AllRulesAllSubLeftOnPath occurrence.path ∧
      instances ≠ [] ∧
      LCS.Finset.ofList instances = mid.1 ∧
      ∀ target, target ∈ instances →
        ∃ substitutions,
          g2nnfUniversalAntecedentLineage occurrence.path
              source target substitutions ∧
            substitutions.map Prod.fst =
              (prenexPrefix source).map Prod.snd ∧
            replayQuantifierSubstitutionsFormula substitutions
              (prenexMatrix source) = target := by
  rcases universalPrenexSingleton_midsequentFullPrefix
      source hSource hDistinct mid hMid with
    ⟨hSuccedent, occurrence, hAbove, hAllSubLeft,
      hInstances⟩
  have hRootNonempty :
      LCS.Finset.singleton source ≠ LCS.Finset.empty := by
    intro hEmpty
    have hSourceMem :
        source ∈ LCS.Finset.singleton source :=
      (LCS.Finset.mem_singleton source source).mpr rfl
    rw [hEmpty] at hSourceMem
    exact LCS.Finset.not_mem_empty hSourceMem
  have hMidNonempty : mid.1 ≠ LCS.Finset.empty :=
    antecedent_ne_empty_of_allSubLeftOnPath
      occurrence.path hAllSubLeft hRootNonempty
  refine ⟨hSuccedent, occurrence, mid.1.toList,
    hAbove, hAllSubLeft,
    finset_toList_ne_nil_of_ne_empty mid.1 hMidNonempty,
    finset_ofList_toList mid.1, ?_⟩
  intro target hTarget
  exact hInstances target
    ((LCS.Finset.mem_toList mid.1 target).mp hTarget)

end LCS.Herbrand.SHGTheorem.Herbrand
end
