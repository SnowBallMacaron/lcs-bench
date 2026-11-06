import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.SharpenedHauptsatz
import LCS.Herbrand.NNFHauptsatz.Renaming.Formulae
import LCS.Herbrand.NNFHauptsatz.Renaming.Sequents
import LCS.Herbrand.NNFHauptsatz.Renaming.Occurrences
import LCS.Herbrand.NNFHauptsatz.Renaming.ProofTrees

/-! # Herbrand.NNFHauptsatz Variable Renaming

Untagged syntax infrastructure for uniformly renaming every variable in a
`FormulaN`, including quantifier binders.  The definitions accept an arbitrary
map `ρ : Nat → Nat`; laws that reflect equality, substitution guards, or
free-variable subtraction explicitly require `Function.Injective ρ`.
-/

namespace LCS.Herbrand.NNFHauptsatz.Renaming
end LCS.Herbrand.NNFHauptsatz.Renaming
