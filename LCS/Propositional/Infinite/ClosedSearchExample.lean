import LCS.Item
import LCS.Util
import LCS.Propositional.Systems.G
import LCS.Propositional.Systems.G.Search
import LCS.Propositional.Systems.G.Search.Fairness
import Attach
import LCS.Propositional.Infinite.Search
import LCS.Propositional.Infinite.Semantics
import LCS.Propositional.Infinite.ClosedSearchExample.ProofsStamp

/-! # Example 3.5.1: a search that terminates with a closed tree
-/
section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

-- ========= Lemma 3.5.1 (companion def): Infinite Path =========



-- ========= Example 3.5.1: Closed Infinite Search =========

/-- Example 3.5.1: The infinite sequent with
    Gamma_0 = <P0, P0=>P1, P1=>P2, ...> and Delta_0 = <Q, P3>.
    The antecedent is: index 0 -> P0, index n+1 -> (Pn => P(n+1)).
    The succedent is: index 0 -> Q (var 0), index 1 -> P3,
    all other indices -> none. -/
@[blueprint "chap3__example_3_5_1" (main := true)]
def exInfSearchClosedAntecedent : InfSequent :=
  { antecedent := fun n =>
      if n = 0 then some (.var 1)
      else some (.impl (.var n) (.var (n + 1)))
    succedent := fun n =>
      if n = 0 then some (.var 0)
      else if n = 1 then some (.var 4)
      else none
    antecedent_noHoles := by
      intro n h
      cases n <;> simp at h
    succedent_noHoles := by
      intro n h
      cases n with
      | zero => simp at h
      | succ n =>
        cases n with
        | zero => simp_all
        | succ n => simp }

/-- Example 3.5.1 (companion): The initial search state for the closed
    example. Tree = leaf (P0 -> Q), L = <P0=>P1, P1=>P2, ...>,
    R = <P3>. -/

@[blueprint "chap3__example_3_5_1"]
def exInfSearchClosedInit : InfSearchState :=
  infSearchInit exInfSearchClosedAntecedent

/-- Example 3.5.1 (companion): The search state after four rounds of
    infExpand. Demonstrates that the infinite search terminates in
    4 rounds on this particular input (all leaves become axioms). -/

@[blueprint "chap3__example_3_5_1"]
def exInfSearchClosedRound4 : InfSearchState :=
  let s0 := exInfSearchClosedInit
  let s1 := infExpand s0
  let s2 := infExpand s1
  let s3 := infExpand s2
  infExpand s3

/-- Example 3.5.1: The displayed initial state. Here var 0 is Q and
    var (i + 1) is Pᵢ; L starts with P₀ ⊃ P₁ and R contains only P₃. -/

@[blueprint "chap3__example_3_5_1"]
def exInfSearchClosedInitDisplayed : InfSearchState :=
  { L := fun n => some (.impl (.var (n + 1)) (.var (n + 2)))
    R := fun n => match n with | 0 => some (.var 4) | _ + 1 => none
    L_noHoles := by intro n h; cases h
    R_noHoles := by intro n h; cases n with | zero => cases h | succ n => rfl
    rootSeq := ⟨[.var 1], [.var 0]⟩
    tree := .leaf ⟨[.var 1], [.var 0]⟩ }

/-- Initialization produces the displayed tree and both remaining streams. -/
@[blueprint "chap3__example_3_5_1"]
theorem exInfSearchClosedInit_eq_displayed :
    exInfSearchClosedInit = exInfSearchClosedInitDisplayed

/-- Example 3.5.1: The complete displayed round-1 state. The tree
    retains all introduction edges and axiom branches; L starts with P₁ ⊃ P₂
    and R is empty. -/

@[blueprint "chap3__example_3_5_1"]
def exInfSearchClosedRound1Displayed : InfSearchState :=
  { L := fun n => some (.impl (.var (n + 2)) (.var (n + 3)))
    R := fun _ => none
    L_noHoles := by intro n h; cases h
    R_noHoles := by intro n h; rfl
    rootSeq := ⟨[.var 1], [.var 0]⟩
    tree := .extend (some (.impl (.var 1) (.var 2))) (some (.var 4))
      (.leaf ⟨[.var 1, .impl (.var 1) (.var 2)], [.var 0, .var 4]⟩) }

/-- One procedure round produces the next complete displayed state. -/
@[blueprint "chap3__example_3_5_1"]
theorem exInfSearchClosedRound1_eq_displayed :
    infExpand exInfSearchClosedInitDisplayed = exInfSearchClosedRound1Displayed

/-- Example 3.5.1: The complete displayed round-2 state. The tree
    retains all introduction edges and axiom branches; L starts with P₂ ⊃ P₃
    and R is empty. -/

@[blueprint "chap3__example_3_5_1"]
def exInfSearchClosedRound2Displayed : InfSearchState :=
  { L := fun n => some (.impl (.var (n + 3)) (.var (n + 4)))
    R := fun _ => none
    L_noHoles := by intro n h; cases h
    R_noHoles := by intro n h; rfl
    rootSeq := ⟨[.var 1], [.var 0]⟩
    tree := .extend (some (.impl (.var 1) (.var 2))) (some (.var 4))
      (.twoPremise (.implLeft [.var 1] [] [.var 0, .var 4] (.var 1) (.var 2))
        (.leaf ⟨[.var 1], [.var 1, .var 0, .var 4]⟩)
        (.extend (some (.impl (.var 2) (.var 3))) none
          (.leaf ⟨[.var 2, .var 1, .impl (.var 2) (.var 3)], [.var 0, .var 4]⟩))) }

/-- One procedure round produces the next complete displayed state. -/
@[blueprint "chap3__example_3_5_1"]
theorem exInfSearchClosedRound2_eq_displayed :
    infExpand exInfSearchClosedRound1Displayed = exInfSearchClosedRound2Displayed

/-- Example 3.5.1: The complete displayed round-3 state. The tree
    retains all introduction edges and axiom branches; L starts with P₃ ⊃ P₄
    and R is empty. -/

@[blueprint "chap3__example_3_5_1"]
def exInfSearchClosedRound3Displayed : InfSearchState :=
  { L := fun n => some (.impl (.var (n + 4)) (.var (n + 5)))
    R := fun _ => none
    L_noHoles := by intro n h; cases h
    R_noHoles := by intro n h; rfl
    rootSeq := ⟨[.var 1], [.var 0]⟩
    tree := .extend (some (.impl (.var 1) (.var 2))) (some (.var 4))
      (.twoPremise (.implLeft [.var 1] [] [.var 0, .var 4] (.var 1) (.var 2))
        (.leaf ⟨[.var 1], [.var 1, .var 0, .var 4]⟩)
        (.extend (some (.impl (.var 2) (.var 3))) none
          (.twoPremise (.implLeft [.var 2, .var 1] [] [.var 0, .var 4] (.var 2) (.var 3))
            (.leaf ⟨[.var 2, .var 1], [.var 2, .var 0, .var 4]⟩)
            (.extend (some (.impl (.var 3) (.var 4))) none
              (.leaf ⟨[.var 3, .var 2, .var 1, .impl (.var 3) (.var 4)], [.var 0, .var 4]⟩))))) }

/-- One procedure round produces the next complete displayed state. -/
@[blueprint "chap3__example_3_5_1"]
theorem exInfSearchClosedRound3_eq_displayed :
    infExpand exInfSearchClosedRound2Displayed = exInfSearchClosedRound3Displayed

/-- Example 3.5.1: The complete displayed round-4 state. The tree
    retains all introduction edges and axiom branches; L starts with P₄ ⊃ P₅
    and R is empty. -/

@[blueprint "chap3__example_3_5_1"]
def exInfSearchClosedRound4Displayed : InfSearchState :=
  { L := fun n => some (.impl (.var (n + 5)) (.var (n + 6)))
    R := fun _ => none
    L_noHoles := by intro n h; cases h
    R_noHoles := by intro n h; rfl
    rootSeq := ⟨[.var 1], [.var 0]⟩
    tree := .extend (some (.impl (.var 1) (.var 2))) (some (.var 4))
      (.twoPremise (.implLeft [.var 1] [] [.var 0, .var 4] (.var 1) (.var 2))
        (.leaf ⟨[.var 1], [.var 1, .var 0, .var 4]⟩)
        (.extend (some (.impl (.var 2) (.var 3))) none
          (.twoPremise (.implLeft [.var 2, .var 1] [] [.var 0, .var 4] (.var 2) (.var 3))
            (.leaf ⟨[.var 2, .var 1], [.var 2, .var 0, .var 4]⟩)
            (.extend (some (.impl (.var 3) (.var 4))) none
              (.twoPremise (.implLeft [.var 3, .var 2, .var 1] [] [.var 0, .var 4] (.var 3) (.var 4))
                (.leaf ⟨[.var 3, .var 2, .var 1], [.var 3, .var 0, .var 4]⟩)
                (.leaf ⟨[.var 4, .var 3, .var 2, .var 1], [.var 0, .var 4]⟩)))))) }

/-- One procedure round produces the next complete displayed state. -/
@[blueprint "chap3__example_3_5_1"]
theorem exInfSearchClosedRound4_eq_displayed :
    infExpand exInfSearchClosedRound3Displayed = exInfSearchClosedRound4Displayed

/-- Example 3.5.1 (companion): A proof tree extracted from the closed
    search tree by propagating introduced propositions upward and
    deleting duplicate nodes. Proves a finite sequent P0, P0=>P1,
    P1=>P2, P2=>P3 -> Q, P3 that witnesses provability of the
    original infinite sequent. -/

@[blueprint "chap3__example_3_5_1"]
def exInfSearchClosedProofTreeSeq : Sequent :=
  Sequent.mk
    [.var 1, .impl (.var 1) (.var 2), .impl (.var 2) (.var 3), .impl (.var 3) (.var 4)]
    [.var 0, .var 4]

/-- The finite proof obtained by propagating the three introduced
implications toward the root and deleting the introduction edges. Its
three implication-left rules are the rules used in the four-round search. -/
@[blueprint "chap3__example_3_5_1"]
def exInfSearchClosedProofTree : ProofTree exInfSearchClosedProofTreeSeq := by
  apply ProofTree.twoPremise (GentzenStep2.implLeft
    [.var 1] [.impl (.var 2) (.var 3), .impl (.var 3) (.var 4)]
    [.var 0, .var 4] (.var 1) (.var 2))
  · exact .axiom_ _ ⟨.var 1, by simp, by simp⟩
  · apply ProofTree.twoPremise (GentzenStep2.implLeft
      [.var 2, .var 1] [.impl (.var 3) (.var 4)]
      [.var 0, .var 4] (.var 2) (.var 3))
    · exact .axiom_ _ ⟨.var 2, by simp, by simp⟩
    · apply ProofTree.twoPremise (GentzenStep2.implLeft
        [.var 3, .var 2, .var 1] [] [.var 0, .var 4] (.var 3) (.var 4))
      · exact .axiom_ _ ⟨.var 3, by simp, by simp⟩
      · exact .axiom_ _ ⟨.var 4, by simp, by simp⟩

/-- Example 3.5.1 closes after the textbook's four rounds. -/
@[blueprint "chap3__example_3_5_1"]
theorem exInfSearchClosedRound4_closed :
    isClosedTree exInfSearchClosedRound4.tree 

end LCS.Propositional.Infinite
end
