import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.NNFHauptsatz.Theorem
import LCS.Herbrand.NNFHauptsatz.Equality
import LCS.Herbrand.SHGTheorem.Herbrand.SyntaxAllocation

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

/-- One exact left-formula occurrence transition through the selected
premise of a G2nnf rule. A substitution is recorded only when the
tracked address is below the quantified principal occurrence that the
rule transforms. Rules on context formulae contribute no substitution.
-/
def g2nnfFormulaOccurrenceStep {L : Language}
    [DecidableEq (FormulaN L)]
    (rule : G2nnfRuleCore L)
    (choice : G2nnfPremiseChoice)
    (before after : FormulaOccurrenceFocus L)
    (substitution : Option (Nat × Term L)) : Prop :=
  let Gamma := g2nnfLeftPremiseContext rule choice
  (focusIsStrictContext rule choice before ∧
      after = before ∧ substitution = none) ∨
  match rule, choice with
  | .conjLeft1 A B _ _, .only =>
    ∃ rest,
      .conj A B ∉ Gamma ∧
      A ∉ Gamma ∧
      before =
        ⟨.conj A B,
          .connectiveLeft :: rest⟩ ∧
      after = ⟨A, rest⟩ ∧ substitution = none
  | .conjLeft2 A B _ _, .only =>
    ∃ rest,
      .conj A B ∉ Gamma ∧
      B ∉ Gamma ∧
      before =
        ⟨.conj A B,
          .connectiveRight :: rest⟩ ∧
      after = ⟨B, rest⟩ ∧ substitution = none
  | .disjLeft A B _ _, .left =>
    ∃ rest,
      .disj A B ∉ Gamma ∧
      A ∉ Gamma ∧
      before =
        ⟨.disj A B,
          .connectiveLeft :: rest⟩ ∧
      after = ⟨A, rest⟩ ∧ substitution = none
  | .disjLeft A B _ _, .right =>
    ∃ rest,
      .disj A B ∉ Gamma ∧
      B ∉ Gamma ∧
      before =
        ⟨.disj A B,
          .connectiveRight :: rest⟩ ∧
      after = ⟨B, rest⟩ ∧ substitution = none
  | .allSubLeft A occurrence x B t _ _ _, .only =>
    (∃ stem rest,
      A ∉ Gamma ∧
      occurrence.replace (formulaSubstN B t x) ∉ Gamma ∧
      before.ambient = A ∧
      before.address =
        stem ++ .quantifierBody :: rest ∧
      stem = maxQuantifierOccurrenceFormulaAddress occurrence ∧
      formulaAtOccurrenceAddress A stem =
        some occurrence.selected ∧
      after =
        ⟨occurrence.replace (formulaSubstN B t x),
          stem ++ rest⟩ ∧
      substitution = some (x, t)) ∨
    (before.ambient = A ∧
      A ∉ Gamma ∧
      occurrence.replace (formulaSubstN B t x) ∉ Gamma ∧
      ¬ addressAtOrBelowExactMaxQuantifier occurrence before.address ∧
      after =
        ⟨occurrence.replace (formulaSubstN B t x),
          before.address⟩ ∧
      substitution = none)
  | .exSubLeft A occurrence x B y _ _ _, .only =>
    (∃ stem rest,
      A ∉ Gamma ∧
      occurrence.replace (formulaSubstN B (.var y) x) ∉ Gamma ∧
      before.ambient = A ∧
      before.address =
        stem ++ .quantifierBody :: rest ∧
      stem = maxQuantifierOccurrenceFormulaAddress occurrence ∧
      formulaAtOccurrenceAddress A stem =
        some occurrence.selected ∧
      after =
        ⟨occurrence.replace (formulaSubstN B (.var y) x),
          stem ++ rest⟩ ∧
      substitution = some (x, .var y)) ∨
    (before.ambient = A ∧
      A ∉ Gamma ∧
      occurrence.replace (formulaSubstN B (.var y) x) ∉ Gamma ∧
      ¬ addressAtOrBelowExactMaxQuantifier occurrence before.address ∧
      after =
        ⟨occurrence.replace (formulaSubstN B (.var y) x),
          before.address⟩ ∧
      substitution = none)
  | _, _ => False

/-- Exact source-occurrence lineage along a selected G2nnf proof path.
The starting focus is supplied by the source allocation address, and
every recursive clause follows the premise constructor stored in the
path. -/
def g2nnfFormulaOccurrenceLineage {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot}
    {node : G2nnfProofTree hL Γnode Δnode} :
    (path : G2nnfProofTree.RootToNodePath root node) →
    FormulaOccurrenceFocus L → FormulaOccurrenceFocus L →
    List (Nat × Term L) → Prop
  | .root _, sourceFocus, targetFocus, substitutions =>
    sourceFocus = targetFocus ∧ substitutions = []
  | .onePremise rule _ _ _ _ path,
      sourceFocus, targetFocus, substitutions =>
    ∃ nextFocus head tail,
      g2nnfFormulaOccurrenceStep rule .only
        sourceFocus nextFocus head ∧
      g2nnfFormulaOccurrenceLineage path nextFocus targetFocus tail ∧
      substitutions = FormulaOccurrenceLineage.prependSubstitution head tail
  | .leftPremise rule _ _ _ _ _ path,
      sourceFocus, targetFocus, substitutions =>
    ∃ nextFocus head tail,
      g2nnfFormulaOccurrenceStep rule .left
        sourceFocus nextFocus head ∧
      g2nnfFormulaOccurrenceLineage path nextFocus targetFocus tail ∧
      substitutions = FormulaOccurrenceLineage.prependSubstitution head tail
  | .rightPremise rule _ _ _ _ _ path,
      sourceFocus, targetFocus, substitutions =>
    ∃ nextFocus head tail,
      g2nnfFormulaOccurrenceStep rule .right
        sourceFocus nextFocus head ∧
      g2nnfFormulaOccurrenceLineage path nextFocus targetFocus tail ∧
      substitutions = FormulaOccurrenceLineage.prependSubstitution head tail

/-- Equality-system mirror of exact source-occurrence lineage. Path steps
carry Core inferences directly; an equality axiom is a leaf and has no
premise occurrence to descend through. -/
def g2nnfEqFormulaOccurrenceLineage {L : Language}
    {hL : L.hasEquality = true} [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL Γroot Δroot}
    {node : G2nnfEqProofTree hL Γnode Δnode} :
    (path : G2nnfEqProofTree.RootToNodePath root node) →
    FormulaOccurrenceFocus L → FormulaOccurrenceFocus L →
    List (Nat × Term L) → Prop
  | .root _, sourceFocus, targetFocus, substitutions =>
    sourceFocus = targetFocus ∧ substitutions = []
  | .onePremise rule _ _ _ _ path,
      sourceFocus, targetFocus, substitutions =>
    ∃ nextFocus head tail,
      g2nnfFormulaOccurrenceStep rule .only
        sourceFocus nextFocus head ∧
      g2nnfEqFormulaOccurrenceLineage path
        nextFocus targetFocus tail ∧
      substitutions = FormulaOccurrenceLineage.prependSubstitution head tail
  | .leftPremise rule _ _ _ _ _ path,
      sourceFocus, targetFocus, substitutions =>
    ∃ nextFocus head tail,
      g2nnfFormulaOccurrenceStep rule .left
        sourceFocus nextFocus head ∧
      g2nnfEqFormulaOccurrenceLineage path
        nextFocus targetFocus tail ∧
      substitutions = FormulaOccurrenceLineage.prependSubstitution head tail
  | .rightPremise rule _ _ _ _ _ path,
      sourceFocus, targetFocus, substitutions =>
    ∃ nextFocus head tail,
      g2nnfFormulaOccurrenceStep rule .right
        sourceFocus nextFocus head ∧
      g2nnfEqFormulaOccurrenceLineage path
        nextFocus targetFocus tail ∧
      substitutions = FormulaOccurrenceLineage.prependSubstitution head tail

/-- Lemma 7.6.2 (helper): The variable/term substitution performed by
one quantifier-for-subformulae rule. The same representation is used
for left and right rules and for universal and existential rules:
polarity affects the proof rule, not replay of its substitution. -/
def quantifierRuleSubstitution? {L : Language} :
    G2nnfRuleCore L → Option (Nat × Term L)
  | .allSubLeft _ _ x _ t _ _ _ => some (x, t)
  | .allSubRight _ _ x _ y _ _ _ => some (x, .var y)
  | .exSubLeft _ _ x _ y _ _ _ => some (x, .var y)
  | .exSubRight _ _ x _ t _ _ _ => some (x, t)
  | _ => none

/-- Equality rules replay a substitution exactly when they are a
`.base` wrapper around one of the four G2nnf quantifier rules.
Equality-axiom rules contribute no substitution. -/
def quantifierEqRuleSubstitution? {L : Language}
    {hL : L.hasEquality = true} :
    G2nnfEqRule L hL → Option (Nat × Term L)
  | .base rule => quantifierRuleSubstitution? rule
  | .eqAxiom _ => none

/-- Replay a root-to-node sequence of quantifier substitutions in
root-to-node order on a term. -/
def replayQuantifierSubstitutionsTerm {L : Language} :
    List (Nat × Term L) → Term L → Term L
  | [], t => t
  | (x, replacement) :: rest, t =>
    replayQuantifierSubstitutionsTerm rest
      (termSubst t replacement x)

/-- Replay a root-to-node sequence of quantifier substitutions in
root-to-node order on a formula. `formulaSubstN` masks a substitution
under a quantifier binding the same variable. -/
def replayQuantifierSubstitutionsFormula {L : Language} :
    List (Nat × Term L) → FormulaN L → FormulaN L
  | [], A => A
  | (x, replacement) :: rest, A =>
    replayQuantifierSubstitutionsFormula rest
      (formulaSubstN A replacement x)

/-- All quantifier substitutions on one occurrence-sensitive G2nnf
root-to-node path, in the order in which the path crosses them. -/
def g2nnfPathQuantifierSubstitutions {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot}
    {node : G2nnfProofTree hL Γnode Δnode} :
    G2nnfProofTree.RootToNodePath root node →
      List (Nat × Term L)
  | .root _ => []
  | .onePremise rule _ _ _ _ path =>
    match quantifierRuleSubstitution? rule with
    | some substitution =>
      substitution :: g2nnfPathQuantifierSubstitutions path
    | none => g2nnfPathQuantifierSubstitutions path
  | .leftPremise rule _ _ _ _ _ path =>
    match quantifierRuleSubstitution? rule with
    | some substitution =>
      substitution :: g2nnfPathQuantifierSubstitutions path
    | none => g2nnfPathQuantifierSubstitutions path
  | .rightPremise rule _ _ _ _ _ path =>
    match quantifierRuleSubstitution? rule with
    | some substitution =>
      substitution :: g2nnfPathQuantifierSubstitutions path
    | none => g2nnfPathQuantifierSubstitutions path

/-- Equality-system counterpart of
`g2nnfPathQuantifierSubstitutions`. -/
def g2nnfEqPathQuantifierSubstitutions {L : Language}
    {hL : L.hasEquality = true} [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL Γroot Δroot}
    {node : G2nnfEqProofTree hL Γnode Δnode} :
    G2nnfEqProofTree.RootToNodePath root node →
      List (Nat × Term L)
  | .root _ => []
  | .onePremise rule _ _ _ _ path =>
    match quantifierRuleSubstitution? rule with
    | some substitution =>
      substitution :: g2nnfEqPathQuantifierSubstitutions path
    | none => g2nnfEqPathQuantifierSubstitutions path
  | .leftPremise rule _ _ _ _ _ path =>
    match quantifierRuleSubstitution? rule with
    | some substitution =>
      substitution :: g2nnfEqPathQuantifierSubstitutions path
    | none => g2nnfEqPathQuantifierSubstitutions path
  | .rightPremise rule _ _ _ _ _ path =>
    match quantifierRuleSubstitution? rule with
    | some substitution =>
      substitution :: g2nnfEqPathQuantifierSubstitutions path
    | none => g2nnfEqPathQuantifierSubstitutions path

/-- The eigenvariables introduced by the strict `∃:left` ancestors on
one exact G2nnf root-to-node path, in outer-to-inner order. The target
node itself is excluded because `.root node` contributes no rule. -/
def g2nnfStrictExSubLeftAncestorEigenvariables {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot}
    {node : G2nnfProofTree hL Γnode Δnode} :
    G2nnfProofTree.RootToNodePath root node → List Nat
  | .root _ => []
  | .onePremise rule _ _ _ _ path =>
    (match rule with
     | .exSubLeft _ _ _ _ y _ _ _ => [y]
     | _ => []) ++
      g2nnfStrictExSubLeftAncestorEigenvariables path
  | .leftPremise rule _ _ _ _ _ path =>
    (match rule with
     | .exSubLeft _ _ _ _ y _ _ _ => [y]
     | _ => []) ++
      g2nnfStrictExSubLeftAncestorEigenvariables path
  | .rightPremise rule _ _ _ _ _ path =>
    (match rule with
     | .exSubLeft _ _ _ _ y _ _ _ => [y]
     | _ => []) ++
      g2nnfStrictExSubLeftAncestorEigenvariables path

/-- Equality-system mirror of
`g2nnfStrictExSubLeftAncestorEigenvariables`. Only an
`exSubLeft` Core path step contributes an ancestor. -/
def g2nnfEqStrictExSubLeftAncestorEigenvariables
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL Γroot Δroot}
    {node : G2nnfEqProofTree hL Γnode Δnode} :
    G2nnfEqProofTree.RootToNodePath root node → List Nat
  | .root _ => []
  | .onePremise rule _ _ _ _ path =>
    (match rule with
     | .exSubLeft _ _ _ _ y _ _ _ => [y]
     | _ => []) ++
      g2nnfEqStrictExSubLeftAncestorEigenvariables path
  | .leftPremise rule _ _ _ _ _ path =>
    (match rule with
     | .exSubLeft _ _ _ _ y _ _ _ => [y]
     | _ => []) ++
      g2nnfEqStrictExSubLeftAncestorEigenvariables path
  | .rightPremise rule _ _ _ _ _ path =>
    (match rule with
     | .exSubLeft _ _ _ _ y _ _ _ => [y]
     | _ => []) ++
      g2nnfEqStrictExSubLeftAncestorEigenvariables path

def replayG2nnfPathTerm {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot}
    {node : G2nnfProofTree hL Γnode Δnode}
    (path : G2nnfProofTree.RootToNodePath root node)
    (t : Term L) : Term L :=
  replayQuantifierSubstitutionsTerm
    (g2nnfPathQuantifierSubstitutions path) t

def replayG2nnfPathFormula {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot}
    {node : G2nnfProofTree hL Γnode Δnode}
    (path : G2nnfProofTree.RootToNodePath root node)
    (A : FormulaN L) : FormulaN L :=
  replayQuantifierSubstitutionsFormula
    (g2nnfPathQuantifierSubstitutions path) A

def replayG2nnfEqPathFormula {L : Language}
    {hL : L.hasEquality = true} [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL Γroot Δroot}
    {node : G2nnfEqProofTree hL Γnode Δnode}
    (path : G2nnfEqProofTree.RootToNodePath root node)
    (A : FormulaN L) : FormulaN L :=
  replayQuantifierSubstitutionsFormula
    (g2nnfEqPathQuantifierSubstitutions path) A

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

/-- Enumerate every G2nnf `∃:left` occurrence below `current`, carrying
its exact path from the fixed outer root. Reused equal subtree values
remain separate list cells because the paths record left/right premise
choices. -/
def g2nnfExSubLeftOccurrencesAux {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    (root : G2nnfProofTree hL Γroot Δroot) :
    {Γcur Δcur : LCS.Finset (FormulaN L)} →
    (current : G2nnfProofTree hL Γcur Δcur) →
    G2nnfProofTree.RootToNodePath root current →
      List (G2nnfExSubLeftOccurrence (hL := hL) root)
  | _, _, .leaf _ _ hOpen _ _, _ => nomatch hOpen
  | _, _, .extraAxiom _ _ hExtra _ _, _ => nomatch hExtra
  | _, _, .axiom_ _ _ _ _, _ => []
  | _, _, .onePremise rule hAdmit hPrem hSC sub, path =>
    match rule with
    | .exSubLeft A occurrence x B y hSelected gamma delta =>
      let subPath := path.trans
        (.onePremise (.exSubLeft A occurrence x B y hSelected gamma delta) hAdmit
          hPrem hSC sub (.root sub))
      ({ ambient := A
         maxOccurrence := occurrence
         boundVar := x
         body := B
         eigenvariable := y
         hSelected := hSelected
         gamma := gamma
         delta := delta
         hPrem := hPrem
         hSC := hSC
         premise := sub
         path := path } :
        G2nnfExSubLeftOccurrence (hL := hL) root) ::
        g2nnfExSubLeftOccurrencesAux (hL := hL) root sub subPath
    | other =>
      let subPath := path.trans
        (.onePremise other hAdmit hPrem hSC sub (.root sub))
      g2nnfExSubLeftOccurrencesAux (hL := hL) root sub subPath
  | _, _, .twoPremise rule hAdmit hPrem hSC sub1 sub2, path =>
    let leftPath := path.trans
      (.leftPremise rule hAdmit hPrem hSC sub1 sub2 (.root sub1))
    let rightPath := path.trans
      (.rightPremise rule hAdmit hPrem hSC sub1 sub2 (.root sub2))
    g2nnfExSubLeftOccurrencesAux (hL := hL) root sub1 leftPath ++
      g2nnfExSubLeftOccurrencesAux (hL := hL) root sub2 rightPath

def g2nnfExSubLeftOccurrences {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Γ Δ) :
    List (G2nnfExSubLeftOccurrence (hL := hL) T) :=
  g2nnfExSubLeftOccurrencesAux (hL := hL) T T (.root T)

/-- Equality-system enumeration, mirroring only
existential-left Core nodes. -/
def g2nnfEqExSubLeftOccurrencesAux {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    (root : G2nnfEqProofTree hL Γroot Δroot) :
    {Γcur Δcur : LCS.Finset (FormulaN L)} →
    (current : G2nnfEqProofTree hL Γcur Δcur) →
    G2nnfEqProofTree.RootToNodePath root current →
      List (G2nnfEqExSubLeftOccurrence (hL := hL) root)
  | _, _, .leaf _ _ hOpen _ _, _ => nomatch hOpen
  | _, _, .extraAxiom _ _ _ _ _, _ => []
  | _, _, .axiom_ _ _ _ _, _ => []
  | _, _, .onePremise rule hAdmit hPrem hSC sub, path =>
    match rule with
    | .exSubLeft A occurrence x B y hSelected gamma delta =>
      let subPath := path.trans
        (.onePremise (.exSubLeft A occurrence x B y hSelected gamma delta) hAdmit
          hPrem hSC sub (.root sub))
      ({ ambient := A
         maxOccurrence := occurrence
         boundVar := x
         body := B
         eigenvariable := y
         hSelected := hSelected
         gamma := gamma
         delta := delta
         hPrem := hPrem
         hSC := hSC
         premise := sub
         path := path } :
        G2nnfEqExSubLeftOccurrence (hL := hL) root) ::
        g2nnfEqExSubLeftOccurrencesAux root sub subPath
    | other =>
      let subPath := path.trans
        (.onePremise other hAdmit hPrem hSC sub (.root sub))
      g2nnfEqExSubLeftOccurrencesAux root sub subPath
  | _, _, .twoPremise rule hAdmit hPrem hSC sub1 sub2, path =>
    let leftPath := path.trans
      (.leftPremise rule hAdmit hPrem hSC sub1 sub2 (.root sub1))
    let rightPath := path.trans
      (.rightPremise rule hAdmit hPrem hSC sub1 sub2 (.root sub2))
    g2nnfEqExSubLeftOccurrencesAux root sub1 leftPath ++
      g2nnfEqExSubLeftOccurrencesAux root sub2 rightPath

def g2nnfEqExSubLeftOccurrences {L : Language}
    {hL : L.hasEquality = true} [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfEqProofTree hL Γ Δ) :
    List (G2nnfEqExSubLeftOccurrence T) :=
  g2nnfEqExSubLeftOccurrencesAux T T (.root T)

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

/-- Enumerate relevant existential-left steps along exactly the
selected G2nnf root-to-node path.  No off-path sibling is traversed. -/
noncomputable def g2nnfRelevantExSubLeftStepsOnPath
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL Γroot Δroot}
    {node : G2nnfProofTree hL Γnode Δnode} :
    G2nnfProofTree.RootToNodePath root node →
      List (RelevantExSubLeftStep L)
  | .root _ => []
  | .onePremise rule _ _ _ _ path =>
      match rule with
      | .exSubLeft A occurrence x B y hSelected _ _ =>
          match Classical.propDecidable (x ∈ formulaFVN B) with
          | .isTrue hRelevant =>
            ({ ambient := A
               maxOccurrence := occurrence
               boundVar := x
               body := B
               eigenvariable := y
               hSelected := hSelected
               hRelevant := hRelevant } :
              RelevantExSubLeftStep L) ::
              g2nnfRelevantExSubLeftStepsOnPath path
          | .isFalse _ =>
            g2nnfRelevantExSubLeftStepsOnPath path
      | _ => g2nnfRelevantExSubLeftStepsOnPath path
  | .leftPremise _ _ _ _ _ _ path =>
      g2nnfRelevantExSubLeftStepsOnPath path
  | .rightPremise _ _ _ _ _ _ path =>
      g2nnfRelevantExSubLeftStepsOnPath path

/-- Equality-system mirror of the exact-path relevant-step
enumeration.  Only `.exSubLeft ...` contributes a cell. -/
noncomputable def g2nnfEqRelevantExSubLeftStepsOnPath
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL Γroot Δroot}
    {node : G2nnfEqProofTree hL Γnode Δnode} :
    G2nnfEqProofTree.RootToNodePath root node →
      List (RelevantExSubLeftStep L)
  | .root _ => []
  | .onePremise rule _ _ _ _ path =>
      match rule with
      | .exSubLeft A occurrence x B y hSelected Gamma Delta =>
          match Classical.propDecidable (x ∈ formulaFVN B) with
          | .isTrue hRelevant =>
            ({ ambient := A
               maxOccurrence := occurrence
               boundVar := x
               body := B
               eigenvariable := y
               hSelected := hSelected
               hRelevant := hRelevant } :
              RelevantExSubLeftStep L) ::
              g2nnfEqRelevantExSubLeftStepsOnPath path
          | .isFalse _ =>
            g2nnfEqRelevantExSubLeftStepsOnPath path
      | _ => g2nnfEqRelevantExSubLeftStepsOnPath path
  | .leftPremise _ _ _ _ _ _ path =>
      g2nnfEqRelevantExSubLeftStepsOnPath path
  | .rightPremise _ _ _ _ _ _ path =>
      g2nnfEqRelevantExSubLeftStepsOnPath path

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
private theorem g2nnfRetentiveAntecedentLineage_of_mem
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
private theorem g2nnfEqRetentiveAntecedentLineage_of_mem
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

/-- Retentive allocation alignment for one relevant existential-left
occurrence at the endpoint of its exact G2nnf lower path.  The dependent
occurrence certificate ties the ambient and selected existential to the
actual endpoint rule, while the site lookup ties one allocation index
simultaneously to its source address, existential binder/body, and
universal scope. -/
def G2nnfRetentiveAllocationBinding
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    {Δroot : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot}
    (occurrence : G2nnfExSubLeftOccurrence (hL := hL) root)
    (i : Fin spec.n) : Prop :=
  occurrence.boundVar ∈ formulaFVN occurrence.body ∧
    g2nnfRetentiveAntecedentLineage
      occurrence.path spec.source occurrence.ambient ∧
    ∃ sourceAddress sourceBody scope,
      (existentialSitesAux spec.source [])[i.val]? =
          some
            (sourceAddress,
              (FormulaN.ex occurrence.boundVar sourceBody, scope)) ∧
        skolemOccurrenceAddress? spec i =
          some sourceAddress ∧
        formulaAtOccurrenceAddress spec.source sourceAddress =
          some (FormulaN.ex occurrence.boundVar sourceBody) ∧
        spec.allocation i =
          (FormulaN.ex occurrence.boundVar sourceBody, scope) ∧
        occurrence.maxOccurrence.selected =
          FormulaN.ex occurrence.boundVar occurrence.body ∧
        spec.skolemScope i = scope ∧
        scope.Nodup

/-- Equality-system mirror of retentive allocation alignment. -/
noncomputable def G2nnfEqRetentiveAllocationBinding
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    {Δroot : LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot}
    (occurrence : G2nnfEqExSubLeftOccurrence root)
    (i : Fin spec.n) : Prop :=
  occurrence.boundVar ∈ formulaFVN occurrence.body ∧
    g2nnfEqRetentiveAntecedentLineage
      occurrence.path spec.source occurrence.ambient ∧
    ∃ sourceAddress sourceBody scope,
      (existentialSitesAux spec.source [])[i.val]? =
          some
            (sourceAddress,
              (FormulaN.ex occurrence.boundVar sourceBody, scope)) ∧
        skolemOccurrenceAddress? spec i =
          some sourceAddress ∧
        formulaAtOccurrenceAddress spec.source sourceAddress =
          some (FormulaN.ex occurrence.boundVar sourceBody) ∧
        spec.allocation i =
          (FormulaN.ex occurrence.boundVar sourceBody, scope) ∧
        occurrence.maxOccurrence.selected =
          FormulaN.ex occurrence.boundVar occurrence.body ∧
        spec.skolemScope i = scope ∧
        scope.Nodup

/-- Every relevant G2nnf existential-left cell in a singleton-source
quantifier path has exactly one source allocation.  The occurrence
certificate fixes the endpoint rule without adding that rule to its strict
ancestor path.  Existence follows the collision-tolerant lineage;
uniqueness and scope `Nodup` follow from the source's rectification
invariant. -/
theorem g2nnfRetentiveAllocationBinding_existsUnique
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    {Δroot : LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot}
    (occurrence : G2nnfExSubLeftOccurrence (hL := hL) root)
    (hQuantifier :
      AllRulesQuantifierOnPath occurrence.path)
    (hRelevant :
      occurrence.boundVar ∈ formulaFVN occurrence.body) :
    ∃ i : Fin spec.n,
      G2nnfRetentiveAllocationBinding spec occurrence i ∧
        ∀ j : Fin spec.n,
          G2nnfRetentiveAllocationBinding spec occurrence j →
            j = i := by
  have hAmbient :
      occurrence.ambient ∈
        LCS.Finset.insert occurrence.ambient occurrence.gamma :=
    LCS.Finset.mem_insert.mpr (Or.inl rfl)
  have hLineage :
      g2nnfRetentiveAntecedentLineage
        occurrence.path spec.source occurrence.ambient :=
    g2nnfRetentiveAntecedentLineage_from_singleton
      occurrence.path hQuantifier hAmbient
  have hAmbientBinder :
      occurrence.boundVar ∈
        existentialBinderSequence occurrence.ambient :=
    maxQuantifierOccurrence_exBinder_mem
      occurrence.maxOccurrence occurrence.hSelected
  have hSourceBinder :
      occurrence.boundVar ∈
        existentialBinderSequence spec.source :=
    g2nnfRetentiveAntecedentLineage_exBinders
      hLineage occurrence.boundVar hAmbientBinder
  obtain ⟨i, sourceBody, scope, hAllocation⟩ :=
    skolemAllocation_exists_of_exBinder spec hSourceBinder
  obtain ⟨sourceAddress, hSite, hAddress, hFormula⟩ :=
    skolem_site_lookup spec i
  have hScope :
      spec.skolemScope i = scope := by
    simp [SkolemSpec.skolemScope, hAllocation]
  have hScopeNodup : scope.Nodup := by
    rw [← hScope]
    exact skolemScope_nodup spec i
  refine ⟨i, ?_, ?_⟩
  · refine
      ⟨hRelevant, hLineage, sourceAddress, sourceBody, scope,
        ?_, hAddress, ?_, hAllocation, occurrence.hSelected,
        hScope, hScopeNodup⟩
    · simpa [hAllocation] using hSite
    · simpa [hAllocation] using hFormula
  · intro j hBinding
    rcases hBinding with
      ⟨_hOtherRelevant, _hOtherLineage,
        otherAddress, otherBody, otherScope, hOtherSite,
        hOtherAddress, hOtherFormula,
        hOtherAllocation, hOtherSelected,
        hOtherScope, hOtherScopeNodup⟩
    exact
      skolemAllocation_index_unique_of_binder spec
        hOtherAllocation hAllocation

/-- Equality-system existence and uniqueness for the same relevant
lower-path cell. -/
theorem g2nnfEqRetentiveAllocationBinding_existsUnique
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L)
    {Δroot : LCS.Finset (FormulaN L)}
    {root : G2nnfEqProofTree hL
      ({spec.source} : LCS.Finset (FormulaN L)) Δroot}
    (occurrence : G2nnfEqExSubLeftOccurrence root)
    (hQuantifier :
      AllRulesQuantifierOnPath_G2nnfEq occurrence.path)
    (hRelevant :
      occurrence.boundVar ∈ formulaFVN occurrence.body) :
    ∃ i : Fin spec.n,
      G2nnfEqRetentiveAllocationBinding spec occurrence i ∧
        ∀ j : Fin spec.n,
          G2nnfEqRetentiveAllocationBinding spec occurrence j →
            j = i := by
  have hAmbient :
      occurrence.ambient ∈
        LCS.Finset.insert occurrence.ambient occurrence.gamma :=
    LCS.Finset.mem_insert.mpr (Or.inl rfl)
  have hLineage :
      g2nnfEqRetentiveAntecedentLineage
        occurrence.path spec.source occurrence.ambient :=
    g2nnfEqRetentiveAntecedentLineage_from_singleton
      occurrence.path hQuantifier hAmbient
  have hAmbientBinder :
      occurrence.boundVar ∈
        existentialBinderSequence occurrence.ambient :=
    maxQuantifierOccurrence_exBinder_mem
      occurrence.maxOccurrence occurrence.hSelected
  have hSourceBinder :
      occurrence.boundVar ∈
        existentialBinderSequence spec.source :=
    g2nnfEqRetentiveAntecedentLineage_exBinders
      hLineage occurrence.boundVar hAmbientBinder
  obtain ⟨i, sourceBody, scope, hAllocation⟩ :=
    skolemAllocation_exists_of_exBinder spec hSourceBinder
  obtain ⟨sourceAddress, hSite, hAddress, hFormula⟩ :=
    skolem_site_lookup spec i
  have hScope :
      spec.skolemScope i = scope := by
    simp [SkolemSpec.skolemScope, hAllocation]
  have hScopeNodup : scope.Nodup := by
    rw [← hScope]
    exact skolemScope_nodup spec i
  refine ⟨i, ?_, ?_⟩
  · refine
      ⟨hRelevant, hLineage, sourceAddress, sourceBody, scope,
        ?_, hAddress, ?_, hAllocation, occurrence.hSelected,
        hScope, hScopeNodup⟩
    · simpa [hAllocation] using hSite
    · simpa [hAllocation] using hFormula
  · intro j hBinding
    rcases hBinding with
      ⟨_hOtherRelevant, _hOtherLineage,
        otherAddress, otherBody, otherScope, hOtherSite,
        hOtherAddress, hOtherFormula,
        hOtherAllocation, hOtherSelected,
        hOtherScope, hOtherScopeNodup⟩
    exact
      skolemAllocation_index_unique_of_binder spec
        hOtherAllocation hAllocation

/-- Exact ordered scope argument at position `k`, after replaying only
the substitutions certified by the source-occurrence lineage. -/
def g2nnfReplayedSkolemArgument {L : Language}
    (spec : SkolemSpec L)
    (substitutions : List (Nat × Term L))
    (i : Fin spec.n) (k : Fin (spec.skolemRank i)) :
    Term spec.language :=
  liftEigenvarBaseTerm spec
    (replayQuantifierSubstitutionsTerm substitutions
      (.var ((spec.skolemScope i).get
        ⟨k.val, by
          exact k.isLt⟩)))

/-- The only admissible Skolem term for allocation `i` and one exact
lineage. Rank zero produces its fresh constant; positive rank produces its fresh
function applied to the replayed ordered scope. Context-rule substitutions
cannot enter the supplied lineage list. -/
def g2nnfReplayedSkolemTerm {L : Language}
    (spec : SkolemSpec L)
    (substitutions : List (Nat × Term L))
    (i : Fin spec.n) : Term spec.language :=
  if hZero : spec.skolemRank i = 0 then
    .const (.inr ⟨i, hZero⟩)
  else
    .func (.inr ⟨i, Nat.pos_of_ne_zero hZero⟩) fun k =>
      g2nnfReplayedSkolemArgument spec substitutions i k

noncomputable def g2nnfEqReplayedSkolemArgument {L : Language}
    (spec : SkolemSpec L)
    (substitutions : List (Nat × Term L))
    (i : Fin spec.n) (k : Fin (spec.skolemRank i)) :
    Term spec.language :=
  g2nnfReplayedSkolemArgument spec substitutions i k

noncomputable def g2nnfEqReplayedSkolemTerm {L : Language}
    (spec : SkolemSpec L)
    (substitutions : List (Nat × Term L))
    (i : Fin spec.n) : Term spec.language :=
  g2nnfReplayedSkolemTerm spec substitutions i

/-- An allocation index is exact for a G2nnf occurrence when its exact
preorder source address has a collision-free lineage to the exact maximal
address carried by the rule occurrence. -/
def G2nnfExactAllocationBinding {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γ Δ}
    (spec : SkolemSpec L) (occ : G2nnfExSubLeftOccurrence (hL := hL) T)
    (i : Fin spec.n) (substitutions : List (Nat × Term L)) : Prop :=
  spec.source ∈ Γ ∧
  occ.ambient ∉ occ.gamma ∧
  ∃ sourceAddress targetAddress,
    skolemOccurrenceAddress? spec i = some sourceAddress ∧
    formulaAtOccurrenceAddress spec.source sourceAddress =
      some (spec.allocation i).1 ∧
    g2nnfFormulaOccurrenceLineage occ.path
      ⟨spec.source, sourceAddress⟩
      ⟨occ.ambient, targetAddress⟩ substitutions ∧
    targetAddress =
      maxQuantifierOccurrenceFormulaAddress occ.maxOccurrence ∧
    formulaAtOccurrenceAddress occ.ambient targetAddress =
      some occ.maxOccurrence.selected ∧
    (∀ (j : Fin spec.n) otherSourceAddress otherSubstitutions,
      skolemOccurrenceAddress? spec j = some otherSourceAddress →
      formulaAtOccurrenceAddress spec.source otherSourceAddress =
        some (spec.allocation j).1 →
      g2nnfFormulaOccurrenceLineage occ.path
        ⟨spec.source, otherSourceAddress⟩
        ⟨occ.ambient, targetAddress⟩ otherSubstitutions →
      j = i) ∧
    (spec.skolemScope i).Nodup

def G2nnfEqExactAllocationBinding {L : Language}
    {hL : L.hasEquality = true} [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfEqProofTree hL Γ Δ}
    (spec : SkolemSpec L) (occ : G2nnfEqExSubLeftOccurrence T)
    (i : Fin spec.n) (substitutions : List (Nat × Term L)) : Prop :=
  spec.source ∈ Γ ∧
  occ.ambient ∉ occ.gamma ∧
  ∃ sourceAddress targetAddress,
    skolemOccurrenceAddress? spec i = some sourceAddress ∧
    formulaAtOccurrenceAddress spec.source sourceAddress =
      some (spec.allocation i).1 ∧
    g2nnfEqFormulaOccurrenceLineage occ.path
      ⟨spec.source, sourceAddress⟩
      ⟨occ.ambient, targetAddress⟩ substitutions ∧
    targetAddress =
      maxQuantifierOccurrenceFormulaAddress occ.maxOccurrence ∧
    formulaAtOccurrenceAddress occ.ambient targetAddress =
      some occ.maxOccurrence.selected ∧
    (∀ (j : Fin spec.n) otherSourceAddress otherSubstitutions,
      skolemOccurrenceAddress? spec j = some otherSourceAddress →
      formulaAtOccurrenceAddress spec.source otherSourceAddress =
        some (spec.allocation j).1 →
      g2nnfEqFormulaOccurrenceLineage occ.path
        ⟨spec.source, otherSourceAddress⟩
        ⟨occ.ambient, targetAddress⟩ otherSubstitutions →
      j = i) ∧
    (spec.skolemScope i).Nodup

/-- Capture-safety at every node that the bottom-up tree alteration may
map, not merely at the root sequent exposed by the staged theorem. -/
def EigenvarSkolemMapFreeForG2nnfTree {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] (spec : SkolemSpec L)
    (eigenvarMap : EigenvarSkolemMap spec) :
    {Γ Δ : LCS.Finset (FormulaN L)} → G2nnfProofTree hL Γ Δ → Prop
  | _, _, .leaf _ _ hOpen _ _ => nomatch hOpen
  | _, _, .extraAxiom _ _ hExtra _ _ => nomatch hExtra
  | _, _, .axiom_ rule _ _ _ =>
    EigenvarSkolemMapFreeForFinset spec eigenvarMap rule.conclusion.1 ∧
      EigenvarSkolemMapFreeForFinset spec eigenvarMap rule.conclusion.2
  | _, _, .onePremise rule _ _ _ sub =>
    EigenvarSkolemMapFreeForFinset spec eigenvarMap rule.conclusion.1 ∧
      EigenvarSkolemMapFreeForFinset spec eigenvarMap rule.conclusion.2 ∧
      EigenvarSkolemMapFreeForG2nnfTree (hL := hL) spec eigenvarMap sub
  | _, _, .twoPremise rule _ _ _ sub1 sub2 =>
    EigenvarSkolemMapFreeForFinset spec eigenvarMap rule.conclusion.1 ∧
      EigenvarSkolemMapFreeForFinset spec eigenvarMap rule.conclusion.2 ∧
      EigenvarSkolemMapFreeForG2nnfTree (hL := hL) spec eigenvarMap sub1 ∧
      EigenvarSkolemMapFreeForG2nnfTree (hL := hL) spec eigenvarMap sub2

noncomputable def EigenvarSkolemMapFreeForG2nnfEqTree {L : Language}
    {hL : L.hasEquality = true} [DecidableEq (FormulaN L)]
    (spec : SkolemSpec L) (eigenvarMap : EigenvarSkolemMap spec) :
    {Γ Δ : LCS.Finset (FormulaN L)} →
      G2nnfEqProofTree hL Γ Δ → Prop
  | _, _, .leaf _ _ hOpen _ _ => nomatch hOpen
  | Gamma, Delta, .extraAxiom _ _ _ _ _ =>
    EigenvarSkolemMapFreeForFinset spec eigenvarMap Gamma ∧
      EigenvarSkolemMapFreeForFinset spec eigenvarMap Delta
  | _, _, .axiom_ rule _ _ _ =>
    EigenvarSkolemMapFreeForFinset spec eigenvarMap rule.conclusion.1 ∧
      EigenvarSkolemMapFreeForFinset spec eigenvarMap rule.conclusion.2
  | _, _, .onePremise rule _ _ _ sub =>
    EigenvarSkolemMapFreeForFinset spec eigenvarMap rule.conclusion.1 ∧
      EigenvarSkolemMapFreeForFinset spec eigenvarMap rule.conclusion.2 ∧
      EigenvarSkolemMapFreeForG2nnfEqTree spec eigenvarMap sub
  | _, _, .twoPremise rule _ _ _ sub1 sub2 =>
    EigenvarSkolemMapFreeForFinset spec eigenvarMap rule.conclusion.1 ∧
      EigenvarSkolemMapFreeForFinset spec eigenvarMap rule.conclusion.2 ∧
      EigenvarSkolemMapFreeForG2nnfEqTree spec eigenvarMap sub1 ∧
      EigenvarSkolemMapFreeForG2nnfEqTree spec eigenvarMap sub2

/-- A map containing exactly the already-final ranges of the strict
`∃:left` ancestors on one G2nnf occurrence path. The biconditional
excludes forward dependencies and occurrences from other branches. -/
def IsG2nnfStrictAncestorEigenvarMap {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γ Δ} (spec : SkolemSpec L)
    (finalMap : EigenvarSkolemMap spec)
    (occ : G2nnfExSubLeftOccurrence (hL := hL) T)
    (ancestorMap : EigenvarSkolemMap spec) : Prop :=
  ∀ y t, ancestorMap y = some t ↔
    y ∈ g2nnfStrictExSubLeftAncestorEigenvariables occ.path ∧
      finalMap y = some t

/-- Equality-system mirror of `IsG2nnfStrictAncestorEigenvarMap`. -/
noncomputable def IsG2nnfEqStrictAncestorEigenvarMap {L : Language}
    {hL : L.hasEquality = true} [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfEqProofTree hL Γ Δ} (spec : SkolemSpec L)
    (finalMap : EigenvarSkolemMap spec)
    (occ : G2nnfEqExSubLeftOccurrence T)
    (ancestorMap : EigenvarSkolemMap spec) : Prop :=
  ∀ y t, ancestorMap y = some t ↔
    y ∈ g2nnfEqStrictExSubLeftAncestorEigenvariables occ.path ∧
      finalMap y = some t

/-- Outer-to-inner canonical construction for a G2nnf occurrence list.
Structural recursion is the well-founded order. At each cell every
strict path ancestor must already occur in `processed`; the raw exact
Skolem term is then composed once with precisely those already-final
ranges. -/
def IsCanonicalEigenvarMapG2nnfOrderedAux {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γ Δ} (spec : SkolemSpec L)
    (eigenvarMap : EigenvarSkolemMap spec) :
    List Nat → List (G2nnfExSubLeftOccurrence (hL := hL) T) → Prop
  | processed, [] => processed.Nodup
  | processed, occ :: rest =>
    (∀ y, y ∈ g2nnfStrictExSubLeftAncestorEigenvariables occ.path →
      y ∈ processed) ∧
    ∃ (i : Fin spec.n) (substitutions : List (Nat × Term L))
        (ancestorMap : EigenvarSkolemMap spec),
      G2nnfExactAllocationBinding spec occ i substitutions ∧
      IsG2nnfStrictAncestorEigenvarMap spec eigenvarMap occ
        ancestorMap ∧
      eigenvarMap occ.eigenvariable =
        some (applyEigenvarSkolemMapTerm spec ancestorMap
          (g2nnfReplayedSkolemTerm spec substitutions i)) ∧
      IsCanonicalEigenvarMapG2nnfOrderedAux spec eigenvarMap
        (occ.eigenvariable :: processed) rest

/-- Equality-system mirror of
`IsCanonicalEigenvarMapG2nnfOrderedAux`. -/
noncomputable def IsCanonicalEigenvarMapG2nnfEqOrderedAux
    {L : Language} {hL : L.hasEquality = true}
    [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    {T : G2nnfEqProofTree hL Γ Δ} (spec : SkolemSpec L)
    (eigenvarMap : EigenvarSkolemMap spec) :
    List Nat → List (G2nnfEqExSubLeftOccurrence T) → Prop
  | processed, [] => processed.Nodup
  | processed, occ :: rest =>
    (∀ y,
      y ∈ g2nnfEqStrictExSubLeftAncestorEigenvariables occ.path →
        y ∈ processed) ∧
    ∃ (i : Fin spec.n) (substitutions : List (Nat × Term L))
        (ancestorMap : EigenvarSkolemMap spec),
      G2nnfEqExactAllocationBinding spec occ i substitutions ∧
      IsG2nnfEqStrictAncestorEigenvarMap spec eigenvarMap occ
        ancestorMap ∧
      eigenvarMap occ.eigenvariable =
        some (applyEigenvarSkolemMapTerm spec ancestorMap
          (g2nnfEqReplayedSkolemTerm spec substitutions i)) ∧
      IsCanonicalEigenvarMapG2nnfEqOrderedAux spec eigenvarMap
        (occ.eigenvariable :: processed) rest

/-- Every final canonical range avoids every variable in the canonical
map domain. Free variables outside that exact domain remain permitted;
this is not a closed-term condition. -/
def EigenvarSkolemMapRangeAvoidsDomain {L : Language}
    (spec : SkolemSpec L) (eigenvarMap : EigenvarSkolemMap spec)
    (domain : List Nat) : Prop :=
  ∀ y t, eigenvarMap y = some t →
    ∀ z, z ∈ domain → ¬ Membership.mem (termFV t) z

/-- Lemma 7.6.2 (companion def): Exact canonical eigenvariable map for
G2nnf. Every path-identified `∃:left` occurrence has a unique
addressed lineage from an allocation occurrence in `spec.source`; its
raw constant-or-function Skolem term is composed with the already-final ranges
of precisely its strict path ancestors. Occurrence paths and
eigenvariables are both `Nodup`; the map has a `some` cell iff the
variable is one of these exact occurrences; and no final range
contains a domain variable. Consequently a one-level public
application is fully composed while unmapped variables remain free. -/
def IsCanonicalEigenvarMapG2nnf {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Γ Δ) (spec : SkolemSpec L)
    (eigenvarMap : EigenvarSkolemMap spec) : Prop :=
  let occurrences := g2nnfExSubLeftOccurrences (hL := hL) T
  occurrences.Nodup ∧
  (occurrences.map fun occ => occ.eigenvariable).Nodup ∧
  IsCanonicalEigenvarMapG2nnfOrderedAux spec eigenvarMap []
    occurrences ∧
  (∀ y, (∃ t, eigenvarMap y = some t) ↔
    y ∈ occurrences.map fun occ => occ.eigenvariable) ∧
  EigenvarSkolemMapRangeAvoidsDomain spec eigenvarMap
    (occurrences.map fun occ => occ.eigenvariable) ∧
  EigenvarSkolemMapFreeForG2nnfTree (hL := hL) spec eigenvarMap T

/-- Equality-system mirror of `IsCanonicalEigenvarMapG2nnf`.
Occurrences are exactly existential-left Core nodes and the same
addressed lineage is followed through equality-system paths. -/
noncomputable def IsCanonicalEigenvarMapG2nnfEq {L : Language}
    {hL : L.hasEquality = true} [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfEqProofTree hL Γ Δ) (spec : SkolemSpec L)
    (eigenvarMap : EigenvarSkolemMap spec) : Prop :=
  let occurrences := g2nnfEqExSubLeftOccurrences T
  occurrences.Nodup ∧
  (occurrences.map fun occ => occ.eigenvariable).Nodup ∧
  IsCanonicalEigenvarMapG2nnfEqOrderedAux spec eigenvarMap []
    occurrences ∧
  (∀ y, (∃ t, eigenvarMap y = some t) ↔
    y ∈ occurrences.map fun occ => occ.eigenvariable) ∧
  EigenvarSkolemMapRangeAvoidsDomain spec eigenvarMap
    (occurrences.map fun occ => occ.eigenvariable) ∧
  EigenvarSkolemMapFreeForG2nnfEqTree spec eigenvarMap T

end LCS.Herbrand.SHGTheorem.Herbrand
end

