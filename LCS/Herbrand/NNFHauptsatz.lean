import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.SyntaxN
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.Semantics.Subformulae
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Equality
import LCS.Herbrand.NNFHauptsatz.Rectification
import LCS.Herbrand.NNFHauptsatz.MaxQuantSubformulae
import LCS.Herbrand.NNFHauptsatz.SubformulaSubstitution
import LCS.Herbrand.NNFHauptsatz.RuleCore
import LCS.Herbrand.NNFHauptsatz.SystemG2nnf
import LCS.Herbrand.NNFHauptsatz.QuantifierPolarity
import LCS.Herbrand.NNFHauptsatz.SystemG2nnfEq

/-! # Herbrand.NNFHauptsatz
    Formalization of Chapter 7, Section 4.1: The System G2nnf.

    Covers Definitions 7.4.1-7.4.3 (maximal quantified subformulae,
    subformula substitution, and the G2nnf Gentzen system),
    and Examples 7.4.1-7.4.3.

    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.Herbrand.NNFHauptsatz
end LCS.Herbrand.NNFHauptsatz
