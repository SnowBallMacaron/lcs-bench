import LCS.Item
import LCS.Util
import LCS.SLD.SLDForm
import LCS.SLD.SLDForm.Occurrence.OccurrenceGCNF
import LCS.SLD.SLDForm.Occurrence.CommutingDiamond
import LCS.SLD.SLDForm.Occurrence.RootPermutation
import LCS.SLD.SLDForm.Occurrence.RootPartition
import LCS.SLD.SLDForm.Occurrence.Compression

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
