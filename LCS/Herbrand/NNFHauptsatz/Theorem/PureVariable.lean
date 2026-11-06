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
import LCS.Herbrand.NNFHauptsatz.Theorem.RootToNodePaths
import LCS.Herbrand.NNFHauptsatz.Theorem.FreshAlphaCopies
import Attach
import LCS.Herbrand.NNFHauptsatz.Theorem.PureVariable.ProofsStamp

/-! # Herbrand.NNFHauptsatz.Theorem.PureVariable

Lemma 7.4.2: pure-variable G2nnf proofs and the conversion of a proof to a
pure-variable proof.
-/

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

/-- Lemma 7.4.2 (companion def): Predicate asserting that a formula `f` appears in some sequent (antecedent or succedent) of a G2nnf proof tree. Used as the G2nnf analog of `proofTreeFormulae` (LK version) — since G2nnf sequents are `LCS.Finset (FormulaN L)` rather than `List (FormulaN L)`, we express tree-containment as a Prop instead of producing a concrete list. The recursion walks the whole tree: at each node, `f` may occur in the current node's conclusion sequent `(Γ, Δ)` (the TYPE INDEX, which is the stored rule's actual conclusion) or in any sub-proof. Indexing note: we pattern-match on the IMPLICIT TYPE INDEX `{Γ Δ}` so that `Γ Δ` here denote the actual conclusion sequent of this node, rather than only the rule's stored side contexts — the rule's conclusion typically inserts the principal formula, so the raw fields miss it. -/
@[blueprint "chap7__lemma_7_4_2"]
def g2nnfProofTreeContainsFormula {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (tree : G2nnfProofTree hL Γ Δ) (f : FormulaN L) : Prop :=
  match tree with
  | .leaf _ _ h _ _ => h.elim
  | .extraAxiom _ _ h _ _ => h.elim
  | .axiom_ _ _ _ _ => f ∈ Γ ∨ f ∈ Δ
  | .onePremise _ _ _ _ sub =>
    f ∈ Γ ∨ f ∈ Δ ∨ g2nnfProofTreeContainsFormula (hL := hL) sub f
  | .twoPremise _ _ _ _ sub1 sub2 =>
    f ∈ Γ ∨ f ∈ Δ ∨
    g2nnfProofTreeContainsFormula (hL := hL) sub1 f ∨
    g2nnfProofTreeContainsFormula (hL := hL) sub2 f

-- ===================================================================
-- Lemma 7.4.2 (companion def): g2nnfNoFreeBoundOverlap
-- ===================================================================

/-- Lemma 7.4.2 (companion def): Predicate asserting that variable `y` does not occur both free and bound in any single formula of the G2nnf proof tree. Checked globally over the whole tree via `g2nnfProofTreeContainsFormula`. -/
@[blueprint "chap7__lemma_7_4_2"]
def g2nnfNoFreeBoundOverlap {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Γ Δ : LCS.Finset (FormulaN L)}
    (y : Nat) (tree : G2nnfProofTree hL Γ Δ) : Prop :=
  ∀ (f : FormulaN L),
    g2nnfProofTreeContainsFormula tree f →
    ¬ (Membership.mem (formulaFVN f) y ∧
       Membership.mem (formulaBVN f) y)

-- ===================================================================
-- Lemma 7.4.2 (companion def): g2nnfEigenvariableOccursOnlyInSubtree
-- ===================================================================

/-- Lemma 7.4.2 (companion def): Every formula occurrence in one sequent is
free of `y`, whether `y` would occur free or bound in that formula. -/
@[blueprint "chap7__lemma_7_4_2"]
def g2nnfSequentVariableFree {L : Language}
    [DecidableEq (FormulaN L)]
    (y : Nat) (Γ Δ : LCS.Finset (FormulaN L)) : Prop :=
  ∀ f : FormulaN L, f ∈ Γ ∨ f ∈ Δ →
    ¬ Membership.mem (formulaAllVariables f) y

/-- Lemma 7.4.2 (companion def): Every formula occurrence at every node of a
G2nnf proof tree is free of `y`.  The recursive definition checks node
occurrences directly instead of collecting formula values into a set. -/
@[blueprint "chap7__lemma_7_4_2"]
def g2nnfProofTreeVariableFree {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] (y : Nat)
    {Γ Δ : LCS.Finset (FormulaN L)}
    (tree : G2nnfProofTree hL Γ Δ) : Prop :=
  match tree with
  | .leaf _ _ h _ _ => h.elim
  | .extraAxiom _ _ h _ _ => h.elim
  | .axiom_ _ _ _ _ =>
    g2nnfSequentVariableFree y Γ Δ
  | .onePremise _ _ _ _ sub =>
    g2nnfSequentVariableFree y Γ Δ ∧
    g2nnfProofTreeVariableFree (hL := hL) y sub
  | .twoPremise _ _ _ _ sub1 sub2 =>
    g2nnfSequentVariableFree y Γ Δ ∧
    g2nnfProofTreeVariableFree (hL := hL) y sub1 ∧
    g2nnfProofTreeVariableFree (hL := hL) y sub2

/-- Lemma 7.4.2 (companion def): Along an exact path to an exempt premise
occurrence, `y` is absent from every ancestor sequent and every off-path
sibling subtree.  Reaching `.root` exempts precisely that target occurrence
and its descendants. -/
@[blueprint "chap7__lemma_7_4_2"]
def g2nnfVariableOccursOnlyAlongPath {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] (y : Nat) :
    {Γroot Δroot Γnode Δnode : LCS.Finset (FormulaN L)} →
    {root : G2nnfProofTree hL Γroot Δroot} →
    {node : G2nnfProofTree hL Γnode Δnode} →
    RootToNodePath root node → Prop
  | _, _, _, _, _, _, .root _ => True
  | _, _, _, _, _, _,
      .onePremise rule hAdmit _ _ _ path =>
    g2nnfSequentVariableFree y
      (rule.conclusion).1
      (rule.conclusion).2 ∧
    g2nnfVariableOccursOnlyAlongPath y path
  | _, _, _, _, _, _,
      .leftPremise rule hAdmit _ _ _ sub2 path =>
    g2nnfSequentVariableFree y
      (rule.conclusion).1
      (rule.conclusion).2 ∧
    g2nnfProofTreeVariableFree (hL := hL) y sub2 ∧
    g2nnfVariableOccursOnlyAlongPath y path
  | _, _, _, _, _, _,
      .rightPremise rule hAdmit _ _ sub1 _ path =>
    g2nnfSequentVariableFree y
      (rule.conclusion).1
      (rule.conclusion).2 ∧
    g2nnfProofTreeVariableFree (hL := hL) y sub1 ∧
    g2nnfVariableOccursOnlyAlongPath y path

/-- Lemma 7.4.2 (companion def): Predicate asserting that variable `y` only
occurs inside one exact subtree occurrence of the ambient G2nnf proof tree.
The `NodeOccurrence` path identifies the premise position of the
eigenvariable-introducing inference.  Formula occurrences in ancestor
sequents and off-path sibling subtrees must be `y`-free; only the target
occurrence and its descendants are exempt.  No formula, sequent, or subtree
equality is used to identify occurrences. -/
@[blueprint "chap7__lemma_7_4_2"]
def g2nnfEigenvariableOccursOnlyInSubtree {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)]
    {Γroot Δroot ΓSub ΔSub : LCS.Finset (FormulaN L)}
    {T : G2nnfProofTree hL Γroot Δroot}
    (y : Nat) (occurrence : NodeOccurrence T ΓSub ΔSub) : Prop :=
  g2nnfVariableOccursOnlyAlongPath y occurrence.path

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

end LCS.Herbrand.NNFHauptsatz.Theorem
end
