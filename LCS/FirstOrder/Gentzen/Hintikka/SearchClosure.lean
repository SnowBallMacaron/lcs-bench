import LCS.Item
import LCS.Util
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.SignedFormulae

/-! # Node expansion by the non-branching rules (Section 5.4.7)

Decomposition of the formulae of a sequent and the search closure step that
applies the non-branching rules to a node, with monotonicity and membership
lemmas. Used by the proof of Theorem 5.4.1.
Source: Logic for Computer Science, Gallier 2015
-/

section
namespace LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.SyntaxN.Variables

/-- Theorem 5.5.1 (companion, UNFAITHFUL — TO REMOVE): Per-formula
antecedent decomposition helper for the pre-refactor `searchClosureStep`
pipeline. Textbook Def 5.4.9 expresses the same case analysis via the
grow-left / grow-right procedures, already formalized faithfully in
`LCS.FirstOrder.Gentzen.Search.NoFunction` (`growLeftAtLeaf` and friends).
Used only by unfaithful Thm 5.5.1 scaffolding. -/
def decomposeAntFormula {L : Language} (A : FormulaN L) (t_c t_d : Term L) :
    List (FormulaN L) × List (FormulaN L) :=
  match A with
  | .conj X Y => ([X, Y], [])
  | .disj _ _ => ([], [])  -- type-B: requires branching, not decomposed
  | .impl _ _ => ([], [])  -- type-B: requires branching, not decomposed
  | .neg X => ([], [X])
  | .all x B => ([formulaSubstN B t_c x], [])
  | .ex x B => ([formulaSubstN B t_d x], [])
  | .predN _ _ => ([], [])
  | .eq_ _ _ _ => ([], [])

-- ===================================================================
-- Normalized decomposition: decomposeSuccFormula
-- ===================================================================

/-- Theorem 5.5.1 (companion, UNFAITHFUL — TO REMOVE): Mirror of
`decomposeAntFormula` for the succedent. Superseded by `growRightAtLeaf`
and friends in `LCS.FirstOrder.Gentzen.Search.NoFunction`. -/
def decomposeSuccFormula {L : Language} (B : FormulaN L) (t_c t_d : Term L) :
    List (FormulaN L) × List (FormulaN L) :=
  match B with
  | .conj _ _ => ([], [])  -- type-B: requires branching, not decomposed
  | .disj X Y => ([], [X, Y])
  | .impl X Y => ([X], [Y])
  | .neg X => ([X], [])
  | .ex x A => ([], [formulaSubstN A t_c x])
  | .all x A => ([], [formulaSubstN A t_d x])
  | .predN _ _ => ([], [])
  | .eq_ _ _ _ => ([], [])

-- ===================================================================
-- Normalized collect helpers
-- ===================================================================

/-- Theorem 5.5.1 (companion, UNFAITHFUL — TO REMOVE): flatMap over
`decomposeAntFormula`'s antecedent output. Used only by unfaithful
Thm 5.5.1 scaffolding. -/
def collectDecompAnt {L : Language} (formulas : List (FormulaN L))
    (t_c t_d : Term L) : List (FormulaN L) :=
  formulas.flatMap (fun A => (decomposeAntFormula A t_c t_d).1)

/-- Theorem 5.5.1 (companion, UNFAITHFUL — TO REMOVE): flatMap over
`decomposeAntFormula`'s succedent output. -/
def collectDecompAntSucc {L : Language} (formulas : List (FormulaN L))
    (t_c t_d : Term L) : List (FormulaN L) :=
  formulas.flatMap (fun A => (decomposeAntFormula A t_c t_d).2)

/-- Theorem 5.5.1 (companion, UNFAITHFUL — TO REMOVE): flatMap over
`decomposeSuccFormula`'s antecedent output. -/
def collectDecompSuccAnt {L : Language} (formulas : List (FormulaN L))
    (t_c t_d : Term L) : List (FormulaN L) :=
  formulas.flatMap (fun B => (decomposeSuccFormula B t_c t_d).1)

/-- Theorem 5.5.1 (companion, UNFAITHFUL — TO REMOVE): flatMap over
`decomposeSuccFormula`'s succedent output. -/
def collectDecompSucc {L : Language} (formulas : List (FormulaN L))
    (t_c t_d : Term L) : List (FormulaN L) :=
  formulas.flatMap (fun B => (decomposeSuccFormula B t_c t_d).2)

-- ===================================================================
-- Normalized search closure step
-- ===================================================================

/-- Theorem 5.5.1 (companion, UNFAITHFUL — TO REMOVE): single-term
closure step from the pre-refactor pipeline. Concatenates decomposed
formulas to the sequent. Superseded by the grow-*TreeInv family +
`extendAllNonaxiomLeaves` in `LCS.FirstOrder.Gentzen.Search.NoFunction`,
which produce actual proof-tree nodes indexed by sequent rather than
flat sequent concatenations. -/
def searchClosureStep1 {L : Language} (prev : Sequent L)
    (t_c : Term L) (t_d : Term L) : Sequent L :=
  { antecedent := prev.antecedent
      ++ collectDecompAnt prev.antecedent t_c t_d
      ++ collectDecompSuccAnt prev.succedent t_c t_d
  , succedent := prev.succedent
      ++ collectDecompAntSucc prev.antecedent t_c t_d
      ++ collectDecompSucc prev.succedent t_c t_d }

/-- Theorem 5.5.1 (companion, UNFAITHFUL — TO REMOVE): many-term
version of `searchClosureStep1`. Same superseded status. -/
def searchClosureStep {L : Language} (prev : Sequent L)
    (t_cs : List (Term L)) (t_d : Term L) : Sequent L :=
  t_cs.foldl (fun acc t_c => searchClosureStep1 acc t_c t_d) prev

end LCS.FirstOrder.Gentzen.Hintikka
end
