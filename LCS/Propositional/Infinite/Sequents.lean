import LCS.Item
import LCS.Util
import LCS.Propositional.Systems.G
import LCS.Propositional.Systems.G.Search
import LCS.Propositional.Systems.G.Search.Fairness
import Attach
import LCS.Propositional.Infinite.Sequents.ProofsStamp

/-! # Infinite sequents (Section 3.5.1)

Possibly infinite formula sequences, the sequents they form, and the
sequence operations head, tail and the predicate atomic.
-/
section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

/-- The empty marker terminates a finite sequence. -/
@[blueprint "chap3__definition_3_5_1"]
def NoHoles (s : Nat → Option PropFormulaNormalized) : Prop :=
  ∀ n, s n = none → s (n + 1) = none

/-- Definition 3.5.1: Finite or countably infinite ordered formula sequences. -/
@[blueprint "chap3__definition_3_5_1"]
structure InfSequent where
  antecedent : Nat → Option PropFormulaNormalized
  succedent : Nat → Option PropFormulaNormalized
  antecedent_noHoles : NoHoles antecedent
  succedent_noHoles : NoHoles succedent

attribute [blueprint "chap3__definition_3_5_1"]
  InfSequent.antecedent_noHoles InfSequent.succedent_noHoles

open LCS.Propositional.Systems.G.Search
namespace InfSeq

/-- Definition 3.5.1 (companion): Returns the element at index 0 of the
    sequence, or none if the sequence is empty at index 0. -/

@[blueprint "chap3__definition_3_5_1"]
def head (s : Nat → Option PropFormulaNormalized) : Option PropFormulaNormalized := s 0

/-- Definition 3.5.1 (companion): Shifts the sequence by one position:
    tail s n = s (n + 1). If s is empty, tail returns the empty
    sequence. -/

@[blueprint "chap3__definition_3_5_1"]
def tail (s : Nat → Option PropFormulaNormalized) : Nat → Option PropFormulaNormalized :=
  fun n => s (n + 1)

end InfSeq
end LCS.Propositional.Infinite
end
