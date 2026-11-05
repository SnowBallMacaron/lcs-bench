import LCS.Item
import Attach
import LCS.FOResolution.Graph.ProofsStamp

/-! # Finite resolution graph carrier

The common graph data for ground resolution and first-order resolution
components. Vertex identity is independent of labels; repeated premise
occurrences can refer to the same vertex.
-/

namespace LCS.FOResolution

universe u v

/-- A finite, connected, rooted binary DAG with labels and inference witnesses.

`none` marks a leaf. A step stores its left and right premise occurrences in
order, together with its witness; the two vertices may coincide. The rank
strictly decreases from a conclusion to either premise, excluding cycles.
Every vertex other than the root has an incoming edge. Together with finiteness
and the rank condition, this ensures that every vertex is reachable from the
root: following incoming edges backwards must terminate at the root.

Labels need not distinguish vertices. Leaf membership, lawful resolution
inferences, and the meaning of witnesses are imposed by the source-specific
ground and first-order contracts. This carrier also admits a single leaf,
including the zero-step empty-clause component. -/
@[blueprint "chap8__example_8_3_1"]
structure ResolutionGraphCore (Label : Type u) (Inference : Type v) where
  /-- Vertices are exactly the finite set `Fin size`. -/
  size : Nat
  /-- The conclusion vertex; its presence makes each component nonempty. -/
  root : Fin size
  /-- The clause or other label carried by each vertex. -/
  label : Fin size → Label
  /-- Ordered premise occurrences and an inference witness, or a leaf. -/
  step : Fin size → Option (Fin size × Fin size × Inference)
  /-- A natural-number rank on vertices. -/
  rank : Fin size → Nat
  /-- Both premise occurrences have strictly smaller rank than the conclusion. -/
  rankDecreases : ∀ node left right witness,
    step node = some (left, right, witness) →
      rank left < rank node ∧ rank right < rank node
  /-- Every non-root vertex occurs as a premise of some step. -/
  rooted : ∀ node, node ≠ root →
    ∃ parent left right witness,
      step parent = some (left, right, witness) ∧ (node = left ∨ node = right)

end LCS.FOResolution
