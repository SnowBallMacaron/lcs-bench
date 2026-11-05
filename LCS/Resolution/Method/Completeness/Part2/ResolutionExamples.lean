import LCS.Item
import LCS.Util
import LCS.Resolution.Method.FiniteGraph
import Attach
import LCS.Resolution.Method.Completeness.Part2.ResolutionExamples.ProofsStamp
import LCS.Resolution.Method.Completeness.Part1
attach_helper_namespace LCS.Resolution.Method.Completeness.Proofs

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

@[blueprint "chap4__example_4_3_5"]
theorem ex435D5_wellFormed (Q : Nat)  :
    (ex435D5 Q).WellFormed 

@[blueprint "chap4__example_4_3_5"]
theorem ex435D5_counts (Q : Nat) :
    (ex435D5 Q).stepCount = 1 ∧ (ex435D5 Q).nodeCount = 3 

@[blueprint "chap4__example_4_3_5"]
theorem ex435D5_rootLabel (Q : Nat) :
    (ex435D5 Q).rootLabel = some (Clause.ofList []) 

@[blueprint "chap4__example_4_3_5"]
def ex435D6 (P Q S : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.pos P, .neg Q], none⟩,
    ⟨Clause.ofList [.neg P, .neg S], none⟩,
    ⟨Clause.ofList [.pos S, .neg Q], none⟩,
    ⟨Clause.ofList [.neg Q, .neg S], some ⟨.pos P, 0, 1⟩⟩,
    ⟨Clause.ofList [.neg Q], some ⟨.neg S, 3, 2⟩⟩], 4⟩



@[blueprint "chap4__example_4_3_5"]
theorem ex435D6_wellFormed (P Q S : Nat) (hPQ : P ≠ Q) (hPS : P ≠ S) (hQS : Q ≠ S) :
    (ex435D6 P Q S).WellFormed 

@[blueprint "chap4__example_4_3_5"]
theorem ex435D6_counts (P Q S : Nat) :
    (ex435D6 P Q S).stepCount = 2 ∧ (ex435D6 P Q S).nodeCount = 5 

@[blueprint "chap4__example_4_3_5"]
theorem ex435D6_rootLabel (P Q S : Nat) :
    (ex435D6 P Q S).rootLabel = some (Clause.ofList [.neg Q]) 

@[blueprint "chap4__example_4_3_5"]
def ex435D7 (P Q S : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.pos P, .neg Q], none⟩,
    ⟨Clause.ofList [.neg P, .neg S], none⟩,
    ⟨Clause.ofList [.pos S, .neg Q], none⟩,
    ⟨Clause.ofList [.pos Q], none⟩,
    ⟨Clause.ofList [.neg Q, .neg S], some ⟨.pos P, 0, 1⟩⟩,
    ⟨Clause.ofList [.neg Q], some ⟨.neg S, 4, 2⟩⟩,
    ⟨Clause.ofList [], some ⟨.neg Q, 5, 3⟩⟩], 6⟩



@[blueprint "chap4__example_4_3_5"]
theorem ex435D7_wellFormed (P Q S : Nat) (hPQ : P ≠ Q) (hPS : P ≠ S) (hQS : Q ≠ S) :
    (ex435D7 P Q S).WellFormed 

@[blueprint "chap4__example_4_3_5"]
theorem ex435D7_counts (P Q S : Nat) :
    (ex435D7 P Q S).stepCount = 3 ∧ (ex435D7 P Q S).nodeCount = 7 

@[blueprint "chap4__example_4_3_5"]
theorem ex435D7_rootLabel (P Q S : Nat) :
    (ex435D7 P Q S).rootLabel = some (Clause.ofList []) 

@[blueprint "chap4__example_4_3_6"]
def ex436D1 (P : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.neg P], none⟩,
    ⟨Clause.ofList [.pos P], none⟩,
    ⟨Clause.ofList [], some ⟨.neg P, 0, 1⟩⟩], 2⟩



@[blueprint "chap4__example_4_3_6"]
theorem ex436D1_wellFormed (P : Nat)  :
    (ex436D1 P).WellFormed 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D1_counts (P : Nat) :
    (ex436D1 P).stepCount = 1 ∧ (ex436D1 P).nodeCount = 3 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D1_rootLabel (P : Nat) :
    (ex436D1 P).rootLabel = some (Clause.ofList []) 

@[blueprint "chap4__example_4_3_6"]
def ex436D2 (Q : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.neg Q], none⟩,
    ⟨Clause.ofList [.pos Q], none⟩,
    ⟨Clause.ofList [], some ⟨.neg Q, 0, 1⟩⟩], 2⟩



@[blueprint "chap4__example_4_3_6"]
theorem ex436D2_wellFormed (Q : Nat)  :
    (ex436D2 Q).WellFormed 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D2_counts (Q : Nat) :
    (ex436D2 Q).stepCount = 1 ∧ (ex436D2 Q).nodeCount = 3 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D2_rootLabel (Q : Nat) :
    (ex436D2 Q).rootLabel = some (Clause.ofList []) 

@[blueprint "chap4__example_4_3_6"]
def ex436D3 (P Q : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.neg P], none⟩,
    ⟨Clause.ofList [.pos P, .pos Q], none⟩,
    ⟨Clause.ofList [.pos Q], some ⟨.neg P, 0, 1⟩⟩], 2⟩



@[blueprint "chap4__example_4_3_6"]
theorem ex436D3_wellFormed (P Q : Nat) (hPQ : P ≠ Q) :
    (ex436D3 P Q).WellFormed 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D3_counts (P Q : Nat) :
    (ex436D3 P Q).stepCount = 1 ∧ (ex436D3 P Q).nodeCount = 3 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D3_rootLabel (P Q : Nat) :
    (ex436D3 P Q).rootLabel = some (Clause.ofList [.pos Q]) 

@[blueprint "chap4__example_4_3_6"]
def ex436D4 (P Q : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.neg P], none⟩,
    ⟨Clause.ofList [.pos P, .pos Q], none⟩,
    ⟨Clause.ofList [.neg Q], none⟩,
    ⟨Clause.ofList [.pos Q], some ⟨.neg P, 0, 1⟩⟩,
    ⟨Clause.ofList [], some ⟨.pos Q, 3, 2⟩⟩], 4⟩



@[blueprint "chap4__example_4_3_6"]
theorem ex436D4_wellFormed (P Q : Nat) (hPQ : P ≠ Q) :
    (ex436D4 P Q).WellFormed 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D4_counts (P Q : Nat) :
    (ex436D4 P Q).stepCount = 2 ∧ (ex436D4 P Q).nodeCount = 5 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D4_rootLabel (P Q : Nat) :
    (ex436D4 P Q).rootLabel = some (Clause.ofList []) 

@[blueprint "chap4__example_4_3_6"]
def ex436D5 (P Q R : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.pos R, .neg P], none⟩,
    ⟨Clause.ofList [.pos P, .pos Q], none⟩,
    ⟨Clause.ofList [.neg Q], none⟩,
    ⟨Clause.ofList [.pos R, .pos Q], some ⟨.neg P, 0, 1⟩⟩,
    ⟨Clause.ofList [.pos R], some ⟨.pos Q, 3, 2⟩⟩], 4⟩



@[blueprint "chap4__example_4_3_6"]
theorem ex436D5_wellFormed (P Q R : Nat) (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    (ex436D5 P Q R).WellFormed 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D5_counts (P Q R : Nat) :
    (ex436D5 P Q R).stepCount = 2 ∧ (ex436D5 P Q R).nodeCount = 5 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D5_rootLabel (P Q R : Nat) :
    (ex436D5 P Q R).rootLabel = some (Clause.ofList [.pos R]) 

@[blueprint "chap4__example_4_3_6"]
def ex436D6 (R : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.neg R], none⟩,
    ⟨Clause.ofList [.pos R], none⟩,
    ⟨Clause.ofList [], some ⟨.neg R, 0, 1⟩⟩], 2⟩



@[blueprint "chap4__example_4_3_6"]
theorem ex436D6_wellFormed (R : Nat)  :
    (ex436D6 R).WellFormed 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D6_counts (R : Nat) :
    (ex436D6 R).stepCount = 1 ∧ (ex436D6 R).nodeCount = 3 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D6_rootLabel (R : Nat) :
    (ex436D6 R).rootLabel = some (Clause.ofList []) 

@[blueprint "chap4__example_4_3_6"]
def ex436D7 (P Q R : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.pos R, .neg P], none⟩,
    ⟨Clause.ofList [.pos P, .pos Q], none⟩,
    ⟨Clause.ofList [.neg Q], none⟩,
    ⟨Clause.ofList [.neg R], none⟩,
    ⟨Clause.ofList [.pos R, .pos Q], some ⟨.neg P, 0, 1⟩⟩,
    ⟨Clause.ofList [.pos R], some ⟨.pos Q, 4, 2⟩⟩,
    ⟨Clause.ofList [], some ⟨.pos R, 5, 3⟩⟩], 6⟩



@[blueprint "chap4__example_4_3_6"]
theorem ex436D7_wellFormed (P Q R : Nat) (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    (ex436D7 P Q R).WellFormed 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D7_counts (P Q R : Nat) :
    (ex436D7 P Q R).stepCount = 3 ∧ (ex436D7 P Q R).nodeCount = 7 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D7_rootLabel (P Q R : Nat) :
    (ex436D7 P Q R).rootLabel = some (Clause.ofList []) 

@[blueprint "chap4__example_4_3_6"]
def ex436D8 (P Q R : Nat) : FiniteGraph :=
  ⟨[⟨Clause.ofList [.pos R, .neg P], none⟩,
    ⟨Clause.ofList [.pos P, .pos Q, .pos R], none⟩,
    ⟨Clause.ofList [.neg Q], none⟩,
    ⟨Clause.ofList [.neg R], none⟩,
    ⟨Clause.ofList [.pos R, .pos Q], some ⟨.neg P, 0, 1⟩⟩,
    ⟨Clause.ofList [.pos R], some ⟨.pos Q, 4, 2⟩⟩,
    ⟨Clause.ofList [], some ⟨.pos R, 5, 3⟩⟩], 6⟩



@[blueprint "chap4__example_4_3_6"]
theorem ex436D8_wellFormed (P Q R : Nat) (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    (ex436D8 P Q R).WellFormed 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D8_counts (P Q R : Nat) :
    (ex436D8 P Q R).stepCount = 3 ∧ (ex436D8 P Q R).nodeCount = 7 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D8_rootLabel (P Q R : Nat) :
    (ex436D8 P Q R).rootLabel = some (Clause.ofList []) 


@[blueprint "chap4__example_4_3_5"]
theorem ex435D1_leavesFrom (P : Nat) :
    (ex435D1 P).LeavesFrom (ClauseSequent.ofList [Clause.ofList [.pos P],
      Clause.ofList [.neg P]]) 

@[blueprint "chap4__example_4_3_5"]
theorem ex435D2_leavesFrom (S : Nat) :
    (ex435D2 S).LeavesFrom (ClauseSequent.ofList [Clause.ofList [.pos S],
      Clause.ofList [.neg S]]) 

@[blueprint "chap4__example_4_3_5"]
theorem ex435D3_leavesFrom (P S : Nat) :
    (ex435D3 P S).LeavesFrom (ClauseSequent.ofList [Clause.ofList [.pos P],
      Clause.ofList [.neg P, .neg S]]) 

@[blueprint "chap4__example_4_3_5"]
theorem ex435D4_leavesFrom (P S : Nat) :
    (ex435D4 P S).LeavesFrom (ClauseSequent.ofList [Clause.ofList [.pos P],
      Clause.ofList [.neg P, .neg S],
      Clause.ofList [.pos S]]) 

@[blueprint "chap4__example_4_3_5"]
theorem ex435D5_leavesFrom (Q : Nat) :
    (ex435D5 Q).LeavesFrom (ClauseSequent.ofList [Clause.ofList [.pos Q],
      Clause.ofList [.neg Q]]) 

@[blueprint "chap4__example_4_3_5"]
theorem ex435D6_leavesFrom (P Q S : Nat) :
    (ex435D6 P Q S).LeavesFrom (ClauseSequent.ofList [Clause.ofList [.pos P, .neg Q],
      Clause.ofList [.neg P, .neg S],
      Clause.ofList [.pos S, .neg Q]]) 

@[blueprint "chap4__example_4_3_5"]
theorem ex435D7_leavesFrom (P Q S : Nat) :
    (ex435D7 P Q S).LeavesFrom (ClauseSequent.ofList [Clause.ofList [.pos P, .neg Q],
      Clause.ofList [.neg P, .neg S],
      Clause.ofList [.pos S, .neg Q],
      Clause.ofList [.pos Q]]) 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D1_leavesFrom (P : Nat) :
    (ex436D1 P).LeavesFrom (ClauseSequent.ofList [Clause.ofList [.neg P],
      Clause.ofList [.pos P]]) 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D2_leavesFrom (Q : Nat) :
    (ex436D2 Q).LeavesFrom (ClauseSequent.ofList [Clause.ofList [.neg Q],
      Clause.ofList [.pos Q]]) 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D3_leavesFrom (P Q : Nat) :
    (ex436D3 P Q).LeavesFrom (ClauseSequent.ofList [Clause.ofList [.neg P],
      Clause.ofList [.pos P, .pos Q]]) 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D4_leavesFrom (P Q : Nat) :
    (ex436D4 P Q).LeavesFrom (ClauseSequent.ofList [Clause.ofList [.neg P],
      Clause.ofList [.pos P, .pos Q],
      Clause.ofList [.neg Q]]) 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D5_leavesFrom (P Q R : Nat) :
    (ex436D5 P Q R).LeavesFrom (ClauseSequent.ofList [Clause.ofList [.pos R, .neg P],
      Clause.ofList [.pos P, .pos Q],
      Clause.ofList [.neg Q]]) 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D6_leavesFrom (R : Nat) :
    (ex436D6 R).LeavesFrom (ClauseSequent.ofList [Clause.ofList [.neg R],
      Clause.ofList [.pos R]]) 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D7_leavesFrom (P Q R : Nat) :
    (ex436D7 P Q R).LeavesFrom (ClauseSequent.ofList [Clause.ofList [.pos R, .neg P],
      Clause.ofList [.pos P, .pos Q],
      Clause.ofList [.neg Q],
      Clause.ofList [.neg R]]) 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D8_leavesFrom (P Q R : Nat) :
    (ex436D8 P Q R).LeavesFrom (ClauseSequent.ofList [Clause.ofList [.pos R, .neg P],
      Clause.ofList [.pos P, .pos Q, .pos R],
      Clause.ofList [.neg Q],
      Clause.ofList [.neg R]]) 

@[blueprint "chap4__example_4_3_5"]
theorem ex435D7_isRefutationFor (P Q S : Nat) (hPQ : P ≠ Q) (hPS : P ≠ S) (hQS : Q ≠ S) :
    (ex435D7 P Q S).IsRefutationFor (ex435Sequent P Q S) 

@[blueprint "chap4__example_4_3_6"]
theorem ex436D8_isRefutationFor (P Q R : Nat) (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    (ex436D8 P Q R).IsRefutationFor (ex436Sequent P Q R) 


/-- The unrestricted atom-substitution reading of D3 fails when P=S. -/
@[blueprint "chap4__example_4_3_5"]
theorem ex435D3_alias_not_wellFormed (P : Nat) :
    ¬ (ex435D3 P P).WellFormed 

/-- The unrestricted substitution Q=R invalidates D5's displayed unit root. -/
@[blueprint "chap4__example_4_3_6"]
theorem ex436D5_alias_not_wellFormed (P Q : Nat) :
    ¬ (ex436D5 P Q Q).WellFormed 

end LCS.Resolution.Method.Completeness
end
end

