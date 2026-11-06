import LCS.SLD.FirstOrder.SLDDerivations
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
import LCS.SLD.FirstOrder.SLDRefutations
import LCS.SLD.FirstOrder.Soundness
import LCS.SLD.FirstOrder.AdditionExample
import LCS.SLD.FirstOrder.Lifting
import LCS.SLD.FirstOrder.HashLanguage
import LCS.SLD.FirstOrder.HornEncoding
import LCS.SLD.FirstOrder.HashGroundAdapter
import LCS.SLD.FirstOrder.GroundInstanceExtraction
import LCS.SLD.FirstOrder.GroundInstanceGroundness
import LCS.SLD.FirstOrder.GroundInstanceSemantics
import LCS.SLD.FirstOrder.PropositionalEncoding
import LCS.SLD.FirstOrder.PropositionalReflection
import LCS.SLD.FirstOrder.Completeness

/-! # SLD.FirstOrder (Section 9.4)
    Source: Logic for Computer Science, Gallier 2015

    First-order SLD-resolution: Horn clauses in PROLOG notation,
    SLD-derivations with unification and separating substitutions,
    soundness and completeness via lifting.
-/
