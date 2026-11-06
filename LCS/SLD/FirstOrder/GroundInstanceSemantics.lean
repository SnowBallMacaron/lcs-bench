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
import LCS.SLD.FirstOrder.Lifting
import LCS.SLD.FirstOrder.HornEncoding
import LCS.SLD.FirstOrder.GroundInstanceExtraction
import LCS.SLD.FirstOrder.GroundInstanceGroundness
import Attach
import LCS.SLD.FirstOrder.GroundInstanceSemantics.ProofsStamp

/-! # Unsatisfiability of the ground instances

Section 9.4.2 (proof of Theorem 9.4.1): the extracted ground clauses and goals, and the transfer of unsatisfiability from the compound instance to them. -/
