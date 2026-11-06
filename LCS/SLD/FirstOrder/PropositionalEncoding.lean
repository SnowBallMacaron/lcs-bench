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
import Attach
import LCS.SLD.FirstOrder.PropositionalEncoding.ProofsStamp

/-! # Propositional encoding of ground Horn clauses

Section 9.4.2 (proof of Theorem 9.4.1): ground atoms numbered as propositional letters, the translation of ground Horn clauses to propositional Horn clauses, and the term-model semantics relating the two. -/
