import LCS.Item
import LCS.Util
import LCS.SLD.SLDForm
import LCS.SLD.SLDForm.Occurrence.Part1
import LCS.SLD.SLDForm.Occurrence.Part2

/-! # SLD.SLDForm.Occurrence

An occurrence-preserving carrier for the Chapter 9 GCNF' arguments.

`GCNFProofTree` is indexed by finite sets of clauses.  That representation is
appropriate for the extensional Chapter 4 calculus, but finite-set union can
identify a selected principal clause with an equal clause already present in
the context.  The permutation arguments in Chapter 9 need to distinguish
those occurrences.  The carrier below records the exact list position changed
by each unary disjunction-left inference and provides a one-way compression
back to the existing finite-set proof tree.

This module deliberately has no inverse from arbitrary `GCNFProofTree`s:
finite-set compression erases occurrence provenance.
-/

namespace LCS.SLD.SLDForm.Occurrence

open LCS.Resolution.GCNF

/-! ## Occurrence-indexed proofs -/


namespace OccurrenceGCNFProof


end OccurrenceGCNFProof

/-! ## Exact root occurrences -/


namespace RootOccurrence


end RootOccurrence

/-! ## Exact root-rule certificates -/

namespace OccurrenceGCNFProof


end OccurrenceGCNFProof

/-! ## Two distinct root positions -/


namespace TwoOccurrenceContext


end TwoOccurrenceContext

/-! ## Atomic two-rule commuting diamond -/


namespace UnaryRuleSquare


end UnaryRuleSquare

/-! ## Structural plans for moving one selected rule to the root -/

namespace OccurrenceGCNFProof


namespace InferencePermutationCertificate

end InferencePermutationCertificate


end OccurrenceGCNFProof

/-! ## Derivations rooted at extensional clause sequents -/


namespace OccurrenceGCNFDerivation


end OccurrenceGCNFDerivation

/-! ## Canonical finite-set erasure -/


namespace OccurrenceGCNFDerivation


end OccurrenceGCNFDerivation

end LCS.SLD.SLDForm.Occurrence
