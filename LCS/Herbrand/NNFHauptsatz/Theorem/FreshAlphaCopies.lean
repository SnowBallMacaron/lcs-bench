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
import LCS.Herbrand.NNFHauptsatz.Theorem.CutFree
import LCS.Herbrand.NNFHauptsatz.Theorem.RootToNodePaths
import Attach
import LCS.Herbrand.NNFHauptsatz.Theorem.FreshAlphaCopies.ProofsStamp

/-! # Herbrand.NNFHauptsatz.Theorem.FreshAlphaCopies

Canonical root-fixed alpha copies of G2nnf proof trees with fresh variables, and
the copies of their paths and node occurrences.
-/
