import LCS.FirstOrder.Basic
import LCS.FirstOrder.Syntax.RankedAlphabet
import LCS.FirstOrder.Syntax.FreeGeneration
import Attach
import LCS.FirstOrder.Syntax.Algebra.ProofsStamp

/-! # The two-sorted alphabet of a first-order language

The sorts and ranks of the symbols listed in the remark following
Definition 5.2.1, and algebras over a many-sorted ranked alphabet.
-/

namespace LCS.FirstOrder.Syntax.Algebra

open LCS.FirstOrder.Basic
open LCS.FirstOrder.ManySorted.CongruenceClosure

/-- Definition 5.2.1 (companion): The two sorts of a first-order alphabet. -/
@[blueprint "chap5__definition_5_2_1"]
inductive FirstOrderSort where
  | term
  | formula
  deriving DecidableEq

/-- Definition 5.2.1 (companion): The disjoint union V ⊕ CS ⊕ FS ⊕ PS ⊕ {⊥}
of symbols in the two-sorted-alphabet remark. -/
@[blueprint "chap5__definition_5_2_1"]
inductive TwoSortedSymbol (L : Language) where
  | var : Nat → TwoSortedSymbol L
  | const : L.constSymbols → TwoSortedSymbol L
  | func : L.funSymbols → TwoSortedSymbol L
  | pred : L.predSymbols → TwoSortedSymbol L
  | bot : TwoSortedSymbol L

/-- Definition 5.2.1 (companion): An algebra over a many-sorted ranked
alphabet has a nonempty carrier for each sort and an operation for each symbol.
An operation accepts exactly the argument sorts in its symbol's rank and
returns a value of the result sort; empty argument lists give constants. -/
@[blueprint "chap5__definition_5_3_1"]
structure MSAlgebra (A : MSRankedAlphabet) : Type 1 where
  carrier : A.SortType → Type
  carrierNonempty : ∀ s, Nonempty (carrier s)
  operation : (f : A.symbols) →
    ((i : Fin (A.argSorts f).length) → carrier ((A.argSorts f).get i)) →
    carrier (A.resultSort f)

end LCS.FirstOrder.Syntax.Algebra

namespace LCS.FirstOrder.Syntax.Algebra

open LCS.FirstOrder.Basic
open LCS.FirstOrder.ManySorted.CongruenceClosure
open LCS.FirstOrder.Syntax.FreeGeneration

/-- Theorem 5.2.2 (companion): A homomorphism preserves every ranked operation. -/
@[blueprint "chap5__theorem_5_2_2"]
structure MSHom {S : MSRankedAlphabet} (A B : MSAlgebra S) where
  map : (s : S.SortType) → A.carrier s → B.carrier s
  preserves : ∀ f args, map (S.resultSort f) (A.operation f args) =
    B.operation f (fun i => map ((S.argSorts f).get i) (args i))

/-- Theorem 5.2.2 (companion): An algebra isomorphism is an operation-preserving
map with a two-sided inverse in each sort. -/
@[blueprint "chap5__theorem_5_2_2"]
structure MSIso {S : MSRankedAlphabet} (A B : MSAlgebra S) extends MSHom A B where
  inv : (s : S.SortType) → B.carrier s → A.carrier s
  leftInv : ∀ s x, inv s (map s x) = x
  rightInv : ∀ s y, map s (inv s y) = y

/-- Theorem 5.2.2 (companion): The signature of the term/formula algebra.
Variables are generators, while A_i and E_i are unary operation symbols. -/
@[blueprint "chap5__theorem_5_2_2"]
inductive SyntaxOperation (L : Language) where
  | const : L.constSymbols → SyntaxOperation L
  | func : L.funSymbols → SyntaxOperation L
  | pred : L.predSymbols → SyntaxOperation L
  | eq : L.hasEquality = true → SyntaxOperation L
  | bot | conj | disj | impl | equiv | neg
  | all : Nat → SyntaxOperation L
  | ex : Nat → SyntaxOperation L

end LCS.FirstOrder.Syntax.Algebra

namespace LCS.FirstOrder.Syntax.Algebra

open LCS.FirstOrder.Basic
open LCS.FirstOrder.ManySorted.CongruenceClosure

/-- Definition 5.3.1 (companion): The nonlogical symbols interpreted by a structure. -/
@[blueprint "chap5__definition_5_3_1"]
inductive NonlogicalSymbol (L : Language) where
  | const : L.constSymbols → NonlogicalSymbol L
  | func : L.funSymbols → NonlogicalSymbol L
  | pred : L.predSymbols → NonlogicalSymbol L

end LCS.FirstOrder.Syntax.Algebra
