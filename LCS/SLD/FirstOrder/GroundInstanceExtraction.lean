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
import Attach
import LCS.SLD.FirstOrder.GroundInstanceExtraction.ProofsStamp

/-! # Extracting ground instances

Section 9.4.2 (proof of Theorem 9.4.1): reading the ground substitution instances of the Horn clauses and goals off the compound instance, and the absence of Skolem functions for Horn inputs. -/
