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

/-! # Herbrand.NNFHauptsatz.Theorem.VariableSupport

Finite variable supports of formulae, sequents, rule annotations and proof trees.
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
namespace LCS.Herbrand.NNFHauptsatz

/-- Complete finite support of a finite sequent. -/
noncomputable def g2nnfSequentVariableSupport {L : Language}
    (S : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) :
    LCS.Finset Nat :=
  LCS.Finset.union (formulaFinsetVariableSupport S.1)
    (formulaFinsetVariableSupport S.2)

namespace MaxQuantifierOccurrence

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

end MaxQuantifierOccurrence
namespace G2nnfRuleCore

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

/-- Complete rule support includes its annotations and every stored context. -/
noncomputable def variableSupport {L : Language} (rule : G2nnfRuleCore L) :
    LCS.Finset Nat := LCS.Finset.union rule.annotationSupport rule.contextSupport

end G2nnfRuleCore
end LCS.Herbrand.NNFHauptsatz
namespace LCS.Herbrand.NNFHauptsatz.G2nnfProofTree

/-! ## Complete proof support and canonical root-fixed alpha copies -/

/-- Complete support contributed by one proof-tree node: its actual
conclusion, every stored side context, and every hidden rule annotation. -/
noncomputable def nodeVariableSupport {L : Language}
    [DecidableEq (FormulaN L)] (rule : G2nnfRuleCore L) : LCS.Finset Nat :=
  LCS.Finset.union (g2nnfSequentVariableSupport rule.conclusion) rule.variableSupport

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

end LCS.Herbrand.NNFHauptsatz.G2nnfProofTree
end
