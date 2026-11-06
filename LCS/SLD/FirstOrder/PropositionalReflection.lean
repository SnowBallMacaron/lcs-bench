import LCS.Item
import LCS.Util
import LCS.SLD.Propositional
import LCS.FOResolution.ClauseForm
import LCS.FOResolution.Unification
import LCS.FOResolution.Method
import LCS.FOResolution.Method.Soundness
import LCS.FOResolution.Method.Completeness
import LCS.Herbrand.SHGTheorem.Main
import LCS.SLD.FirstOrder.HornClauses
import LCS.SLD.FirstOrder.Soundness
import LCS.SLD.FirstOrder.Lifting
import LCS.SLD.FirstOrder.PropositionalEncoding
import Attach
import LCS.SLD.FirstOrder.PropositionalReflection.ProofsStamp

/-! # From propositional to ground SLD-refutations

Section 9.4.2 (proof of Theorem 9.4.1): reflecting a propositional SLD-refutation of the encoded clauses, step by step, into a ground SLD transcript. -/
