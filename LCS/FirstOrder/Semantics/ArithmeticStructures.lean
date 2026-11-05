import Init.Data.Rat.Basic
import LCS.FirstOrder.Syntax
import Attach
import LCS.FirstOrder.Semantics.ArithmeticStructures.ProofsStamp

/-! # Arithmetic structures

The rational-number structure for the predicate-free arithmetic language
of Example 5.3.1.
-/

open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax

namespace LCS.FirstOrder.Semantics

/-- Example 5.3.1 (companion): The structure 𝒬 for the predicate-free arithmetic
language with domain Rat. The constant 0 is interpreted as rational zero,
S as q ↦ q + 1, + as rational addition, and * as rational multiplication. -/
@[blueprint "chap5__example_5_3_1" (main := true)]
def peanoRatStructure : Structure peanoLanguage where
  carrier := Rat
  carrierNonempty := ⟨0⟩
  interpFunc
    | ArithFunc.succ, args => args ⟨0, by decide⟩ + 1
    | ArithFunc.plus, args =>
        args ⟨0, by decide⟩ + args ⟨1, by decide⟩
    | ArithFunc.times, args =>
        args ⟨0, by decide⟩ * args ⟨1, by decide⟩
  interpConst
    | ArithConst.zero => 0
  interpPred := fun p => Empty.elim p

end LCS.FirstOrder.Semantics
