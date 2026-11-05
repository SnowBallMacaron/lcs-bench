import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.SharpenedHauptsatz
import LCS.Herbrand.NNFHauptsatz.Renaming.Part1
import LCS.Herbrand.NNFHauptsatz.Renaming.Part2

/-! # Herbrand.NNFHauptsatz Variable Renaming

Untagged syntax infrastructure for uniformly renaming every variable in a
`FormulaN`, including quantifier binders.  The definitions accept an arbitrary
map `ρ : Nat → Nat`; laws that reflect equality, substitution guards, or
free-variable subtraction explicitly require `Function.Injective ρ`.
-/

namespace LCS.Herbrand.NNFHauptsatz

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.SharpenedHauptsatz


namespace MaxQuantifierOccurrence


end MaxQuantifierOccurrence


namespace G2nnfRuleCore


end G2nnfRuleCore

namespace G2nnfProofTree


end G2nnfProofTree

end LCS.Herbrand.NNFHauptsatz
