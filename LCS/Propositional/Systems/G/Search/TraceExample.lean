import LCS.Item
import LCS.Util
import LCS.Propositional.Systems.G
import Attach
import LCS.Propositional.Systems.G.Search.Procedure
import LCS.Propositional.Systems.G.Search.TraceExample.ProofsStamp

/-! # Example 3.4.4: a run of procedure search
-/
section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
variable {mode : SearchMode}

-- ========= Example 3.4.4: Search procedure trace =========

/-- Example 3.4.4: The input sequent
    (P and neg Q), (P implies Q), (T implies R), (P and S) -> T,
    using PropFormulaNormalized constructors with var 0 = P, var 1 = Q, var 2 = R,
    var 3 = S, var 4 = T. -/
@[blueprint "chap3__example_3_4_4" (main := true)]
def exSearchTraceSequent : Sequent :=
  let p := PropFormulaNormalized.var 0
  let q := PropFormulaNormalized.var 1
  let r := PropFormulaNormalized.var 2
  let s := PropFormulaNormalized.var 3
  let t := PropFormulaNormalized.var 4
  Sequent.mk
    [.conj p (.neg q), .impl p q, .impl t r, .conj p s]
    [t]

/-- Example 3.4.4 (companion): The deduction tree after the first round
    of the search procedure applied to exSearchTraceSequent. Expands each
    nonatomic formula in the antecedent: (P and neg Q) via andLeft,
    (P implies Q) via implLeft, (T implies R) via implLeft,
    (P and S) via andLeft. -/
@[blueprint "chap3__example_3_4_4"]
def exSearchTraceRound1 : DeductionTree exSearchTraceSequent :=
  searchRound .systematic (DeductionTree.leaf exSearchTraceSequent)

/-- Example 3.4.4 (companion): The finished deduction tree after the
    second round, which expands the remaining nonatomic formula (neg Q)
    via negLeft in each unfinished leaf. All leaves are now finished
    (either axioms or fully atomic). This is the systematic deduction
    tree. -/
@[blueprint "chap3__example_3_4_4"]
def exSearchTraceRound2 : DeductionTree exSearchTraceSequent :=
  searchRound .systematic exSearchTraceRound1

/-- Example 3.4.4: The complete displayed round-1 tree, including
    the unchanged axiom branch Γ → Δ and every internal rule node. -/
@[blueprint "chap3__example_3_4_4"]
def exSearchTraceRound1Displayed : DeductionTree exSearchTraceSequent :=
  let p := PropFormulaNormalized.var 0
  let q := PropFormulaNormalized.var 1
  let r := PropFormulaNormalized.var 2
  let s := PropFormulaNormalized.var 3
  let t := PropFormulaNormalized.var 4
  .onePremise (.andLeft [] [.impl p q, .impl t r, .conj p s] [t] p (.neg q))
    (.twoPremise (.implLeft [p, .neg q] [.impl t r, .conj p s] [t] p q)
      (.leaf ⟨[p, .neg q, .impl t r, .conj p s], [p, t]⟩)
      (.twoPremise (.implLeft [q, p, .neg q] [.conj p s] [t] t r)
        (.onePremise (.andLeft [q, p, .neg q] [] [t, t] p s)
          (.leaf ⟨[q, p, .neg q, p, s], [t, t]⟩))
        (.onePremise (.andLeft [r, q, p, .neg q] [] [t] p s)
          (.leaf ⟨[r, q, p, .neg q, p, s], [t]⟩))))

/-- The search procedure produces the complete round-1 display. -/
@[blueprint "chap3__example_3_4_4"]
theorem exSearchTraceRound1_eq_displayed :
    exSearchTraceRound1 = exSearchTraceRound1Displayed

/-- Example 3.4.4: The complete displayed round-2 tree, including
    the unchanged axiom branch Γ → Δ and every internal rule node. -/
@[blueprint "chap3__example_3_4_4"]
def exSearchTraceRound2Displayed : DeductionTree exSearchTraceSequent :=
  let p := PropFormulaNormalized.var 0
  let q := PropFormulaNormalized.var 1
  let r := PropFormulaNormalized.var 2
  let s := PropFormulaNormalized.var 3
  let t := PropFormulaNormalized.var 4
  .onePremise (.andLeft [] [.impl p q, .impl t r, .conj p s] [t] p (.neg q))
    (.twoPremise (.implLeft [p, .neg q] [.impl t r, .conj p s] [t] p q)
      (.leaf ⟨[p, .neg q, .impl t r, .conj p s], [p, t]⟩)
      (.twoPremise (.implLeft [q, p, .neg q] [.conj p s] [t] t r)
        (.onePremise (.andLeft [q, p, .neg q] [] [t, t] p s)
          (.onePremise (.negLeft [q, p] [p, s] [t, t] q)
            (.leaf ⟨[q, p, p, s], [q, t, t]⟩)))
        (.onePremise (.andLeft [r, q, p, .neg q] [] [t] p s)
          (.onePremise (.negLeft [r, q, p] [p, s] [t] q)
            (.leaf ⟨[r, q, p, p, s], [q, t]⟩)))))

/-- The search procedure produces the complete round-2 display. -/
@[blueprint "chap3__example_3_4_4"]
theorem exSearchTraceRound2_eq_displayed :
    exSearchTraceRound2 = exSearchTraceRound2Displayed

end LCS.Propositional.Systems.G.Search
end
