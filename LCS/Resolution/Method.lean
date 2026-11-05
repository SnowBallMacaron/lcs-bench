import LCS.Item
import LCS.Util
import LCS.Resolution.GCNF
import Attach
import LCS.Resolution.Method.Part1
import LCS.Resolution.Method.Part2

/-! # Resolution.Method (Sections 4.3.1-4.3.3)
    Source: Logic for Computer Science, Gallier 2015

    Directed acyclic graphs (DAGs) for resolution proofs,
    the resolution method (resolvent, resolution DAG, resolution refutation),
    and soundness of resolution.
-/

namespace LCS.Resolution.Method

open LCS (TreeAddr TreeDomain LabeledTree)
open LCS.Resolution.GCNF

-- ========= Example 4.3.2: DAGs =========


-- ========= Definition 4.3.1 (companion defs): DAG nodes, edges, etc. =========

namespace DAG


-- ATTACH-BLOCKER: variable
variable {Delta : Type}



end DAG

-- ========= Definition 4.3.2: Resolvent =========

namespace Clause


end Clause

-- ========= Definition 4.3.3 (companion defs): Labels, leaves, refutation =========

namespace ResolutionDAG



end ResolutionDAG


namespace ResolutionForest


end ResolutionForest

-- ========= ResolutionTree: inductive resolution proof structure =========


namespace ResolutionTree

open LCS.Resolution.GCNF







end ResolutionTree

namespace Clause


end Clause

-- ========= Lemma 4.3.1 (supporting defs): Satisfaction =========

namespace Clause


end Clause

namespace ClauseSet


end ClauseSet

-- ========= Definition 4.3.2 (companion): Unsatisfiability =========

namespace ClauseSet


end ClauseSet

-- ========= Example 4.3.1: Concrete Labeled Tree =========


-- ========= Example 4.3.3: Multiple Resolvents =========

open LCS.Resolution.GCNF








-- ========= Resolvent satisfaction helper =========



open LCS.Propositional.Syntax LCS.Propositional.Semantics




end LCS.Resolution.Method
