import LCS.Resolution.Method.Completeness.Part2.ResolutionExamples

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

helper theorem Completeness.ex435D5_allRowsWellFormed (Q : Nat)  :
    (ex435D5 Q).AllRowsWellFormed := by
  refine ⟨by simp [ex435D5], ?_⟩
  intro i n hn r hr
  have hi : i < 3 := by
    have := (List.getElem?_eq_some_iff.mp hn).1
    simpa [FiniteGraph.node, ex435D5] using this
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  all_goals simp only [FiniteGraph.node, ex435D5, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.some.injEq] at hn
  all_goals subst n
  all_goals cases hr
  all_goals refine ⟨by simp, by simp, _, _, rfl, rfl, ?_, ?_, ?_⟩
  all_goals
    first
    | solve | simp [Clause.ofList, Literal.conjugate]
    | apply LCS.Finset.ext
      intro L
      cases L with
      | pos k =>
        by_cases hQ : k = Q <;>
          simp_all [GCNF.Clause.union, GCNF.Clause.remove, Clause.ofList, Literal.conjugate]
      | neg k =>
        by_cases hQ : k = Q <;>
          simp_all [GCNF.Clause.union, GCNF.Clause.remove, Clause.ofList, Literal.conjugate]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex435D5_wellFormed := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  (ex435D5_allRowsWellFormed Q ).wellFormed

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex435D5_counts := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    constructor <;> rfl

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex435D5_rootLabel := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  rfl

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

helper theorem Completeness.ex435D6_allRowsWellFormed (P Q S : Nat) (hPQ : P ≠ Q) (hPS : P ≠ S) (hQS : Q ≠ S) :
    (ex435D6 P Q S).AllRowsWellFormed := by
  refine ⟨by simp [ex435D6], ?_⟩
  intro i n hn r hr
  have hi : i < 5 := by
    have := (List.getElem?_eq_some_iff.mp hn).1
    simpa [FiniteGraph.node, ex435D6] using this
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [FiniteGraph.node, ex435D6, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.some.injEq] at hn
  all_goals subst n
  all_goals cases hr
  all_goals refine ⟨by simp, by simp, _, _, rfl, rfl, ?_, ?_, ?_⟩
  all_goals
    first
    | solve | simp [Clause.ofList, Literal.conjugate]
    | apply LCS.Finset.ext
      intro L
      cases L with
      | pos k =>
        by_cases hP : k = P <;> by_cases hQ : k = Q <;> by_cases hS : k = S <;>
          simp_all [GCNF.Clause.union, GCNF.Clause.remove, Clause.ofList, Literal.conjugate]
      | neg k =>
        by_cases hP : k = P <;> by_cases hQ : k = Q <;> by_cases hS : k = S <;>
          simp_all [GCNF.Clause.union, GCNF.Clause.remove, Clause.ofList, Literal.conjugate]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex435D6_wellFormed := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  (ex435D6_allRowsWellFormed P Q S hPQ hPS hQS).wellFormed

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex435D6_counts := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    constructor <;> rfl

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex435D6_rootLabel := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  rfl

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

helper theorem Completeness.ex435D7_allRowsWellFormed (P Q S : Nat) (hPQ : P ≠ Q) (hPS : P ≠ S) (hQS : Q ≠ S) :
    (ex435D7 P Q S).AllRowsWellFormed := by
  refine ⟨by simp [ex435D7], ?_⟩
  intro i n hn r hr
  have hi : i < 7 := by
    have := (List.getElem?_eq_some_iff.mp hn).1
    simpa [FiniteGraph.node, ex435D7] using this
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [FiniteGraph.node, ex435D7, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.some.injEq] at hn
  all_goals subst n
  all_goals cases hr
  all_goals refine ⟨by simp, by simp, _, _, rfl, rfl, ?_, ?_, ?_⟩
  all_goals
    first
    | solve | simp [Clause.ofList, Literal.conjugate]
    | apply LCS.Finset.ext
      intro L
      cases L with
      | pos k =>
        by_cases hP : k = P <;> by_cases hQ : k = Q <;> by_cases hS : k = S <;>
          simp_all [GCNF.Clause.union, GCNF.Clause.remove, Clause.ofList, Literal.conjugate]
      | neg k =>
        by_cases hP : k = P <;> by_cases hQ : k = Q <;> by_cases hS : k = S <;>
          simp_all [GCNF.Clause.union, GCNF.Clause.remove, Clause.ofList, Literal.conjugate]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex435D7_wellFormed := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  (ex435D7_allRowsWellFormed P Q S hPQ hPS hQS).wellFormed

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex435D7_counts := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    constructor <;> rfl

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex435D7_rootLabel := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  rfl

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

helper theorem Completeness.ex436D1_allRowsWellFormed (P : Nat)  :
    (ex436D1 P).AllRowsWellFormed := by
  refine ⟨by simp [ex436D1], ?_⟩
  intro i n hn r hr
  have hi : i < 3 := by
    have := (List.getElem?_eq_some_iff.mp hn).1
    simpa [FiniteGraph.node, ex436D1] using this
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  all_goals simp only [FiniteGraph.node, ex436D1, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.some.injEq] at hn
  all_goals subst n
  all_goals cases hr
  all_goals refine ⟨by simp, by simp, _, _, rfl, rfl, ?_, ?_, ?_⟩
  all_goals
    first
    | solve | simp [Clause.ofList, Literal.conjugate]
    | apply LCS.Finset.ext
      intro L
      cases L with
      | pos k =>
        by_cases hP : k = P <;>
          simp_all [GCNF.Clause.union, GCNF.Clause.remove, Clause.ofList, Literal.conjugate]
      | neg k =>
        by_cases hP : k = P <;>
          simp_all [GCNF.Clause.union, GCNF.Clause.remove, Clause.ofList, Literal.conjugate]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D1_wellFormed := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  (ex436D1_allRowsWellFormed P ).wellFormed

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D1_counts := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    constructor <;> rfl

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D1_rootLabel := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  rfl

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

helper theorem Completeness.ex436D2_allRowsWellFormed (Q : Nat)  :
    (ex436D2 Q).AllRowsWellFormed := by
  refine ⟨by simp [ex436D2], ?_⟩
  intro i n hn r hr
  have hi : i < 3 := by
    have := (List.getElem?_eq_some_iff.mp hn).1
    simpa [FiniteGraph.node, ex436D2] using this
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  all_goals simp only [FiniteGraph.node, ex436D2, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.some.injEq] at hn
  all_goals subst n
  all_goals cases hr
  all_goals refine ⟨by simp, by simp, _, _, rfl, rfl, ?_, ?_, ?_⟩
  all_goals
    first
    | solve | simp [Clause.ofList, Literal.conjugate]
    | apply LCS.Finset.ext
      intro L
      cases L with
      | pos k =>
        by_cases hQ : k = Q <;>
          simp_all [GCNF.Clause.union, GCNF.Clause.remove, Clause.ofList, Literal.conjugate]
      | neg k =>
        by_cases hQ : k = Q <;>
          simp_all [GCNF.Clause.union, GCNF.Clause.remove, Clause.ofList, Literal.conjugate]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D2_wellFormed := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  (ex436D2_allRowsWellFormed Q ).wellFormed

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D2_counts := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    constructor <;> rfl

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D2_rootLabel := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  rfl

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

helper theorem Completeness.ex436D3_allRowsWellFormed (P Q : Nat) (hPQ : P ≠ Q) :
    (ex436D3 P Q).AllRowsWellFormed := by
  refine ⟨by simp [ex436D3], ?_⟩
  intro i n hn r hr
  have hi : i < 3 := by
    have := (List.getElem?_eq_some_iff.mp hn).1
    simpa [FiniteGraph.node, ex436D3] using this
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  all_goals simp only [FiniteGraph.node, ex436D3, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.some.injEq] at hn
  all_goals subst n
  all_goals cases hr
  all_goals refine ⟨by simp, by simp, _, _, rfl, rfl, ?_, ?_, ?_⟩
  all_goals
    first
    | solve | simp [Clause.ofList, Literal.conjugate]
    | apply LCS.Finset.ext
      intro L
      cases L with
      | pos k =>
        by_cases hP : k = P <;> by_cases hQ : k = Q <;>
          simp_all [GCNF.Clause.union, GCNF.Clause.remove, Clause.ofList, Literal.conjugate]
      | neg k =>
        by_cases hP : k = P <;> by_cases hQ : k = Q <;>
          simp_all [GCNF.Clause.union, GCNF.Clause.remove, Clause.ofList, Literal.conjugate]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D3_wellFormed := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  (ex436D3_allRowsWellFormed P Q hPQ).wellFormed

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D3_counts := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    constructor <;> rfl

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D3_rootLabel := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  rfl

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

helper theorem Completeness.ex436D4_allRowsWellFormed (P Q : Nat) (hPQ : P ≠ Q) :
    (ex436D4 P Q).AllRowsWellFormed := by
  refine ⟨by simp [ex436D4], ?_⟩
  intro i n hn r hr
  have hi : i < 5 := by
    have := (List.getElem?_eq_some_iff.mp hn).1
    simpa [FiniteGraph.node, ex436D4] using this
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [FiniteGraph.node, ex436D4, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.some.injEq] at hn
  all_goals subst n
  all_goals cases hr
  all_goals refine ⟨by simp, by simp, _, _, rfl, rfl, ?_, ?_, ?_⟩
  all_goals
    first
    | solve | simp [Clause.ofList, Literal.conjugate]
    | apply LCS.Finset.ext
      intro L
      cases L with
      | pos k =>
        by_cases hP : k = P <;> by_cases hQ : k = Q <;>
          simp_all [GCNF.Clause.union, GCNF.Clause.remove, Clause.ofList, Literal.conjugate]
      | neg k =>
        by_cases hP : k = P <;> by_cases hQ : k = Q <;>
          simp_all [GCNF.Clause.union, GCNF.Clause.remove, Clause.ofList, Literal.conjugate]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D4_wellFormed := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  (ex436D4_allRowsWellFormed P Q hPQ).wellFormed

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D4_counts := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    constructor <;> rfl

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D4_rootLabel := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  rfl

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

helper theorem Completeness.ex436D5_allRowsWellFormed (P Q R : Nat) (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    (ex436D5 P Q R).AllRowsWellFormed := by
  refine ⟨by simp [ex436D5], ?_⟩
  intro i n hn r hr
  have hi : i < 5 := by
    have := (List.getElem?_eq_some_iff.mp hn).1
    simpa [FiniteGraph.node, ex436D5] using this
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [FiniteGraph.node, ex436D5, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.some.injEq] at hn
  all_goals subst n
  all_goals cases hr
  all_goals refine ⟨by simp, by simp, _, _, rfl, rfl, ?_, ?_, ?_⟩
  all_goals
    first
    | solve | simp [Clause.ofList, Literal.conjugate]
    | apply LCS.Finset.ext
      intro L
      cases L with
      | pos k =>
        by_cases hP : k = P <;> by_cases hQ : k = Q <;> by_cases hR : k = R <;>
          simp_all [GCNF.Clause.union, GCNF.Clause.remove, Clause.ofList, Literal.conjugate]
      | neg k =>
        by_cases hP : k = P <;> by_cases hQ : k = Q <;> by_cases hR : k = R <;>
          simp_all [GCNF.Clause.union, GCNF.Clause.remove, Clause.ofList, Literal.conjugate]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D5_wellFormed := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  (ex436D5_allRowsWellFormed P Q R hPQ hPR hQR).wellFormed

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D5_counts := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    constructor <;> rfl

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D5_rootLabel := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  rfl

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

helper theorem Completeness.ex436D6_allRowsWellFormed (R : Nat)  :
    (ex436D6 R).AllRowsWellFormed := by
  refine ⟨by simp [ex436D6], ?_⟩
  intro i n hn r hr
  have hi : i < 3 := by
    have := (List.getElem?_eq_some_iff.mp hn).1
    simpa [FiniteGraph.node, ex436D6] using this
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  all_goals simp only [FiniteGraph.node, ex436D6, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.some.injEq] at hn
  all_goals subst n
  all_goals cases hr
  all_goals refine ⟨by simp, by simp, _, _, rfl, rfl, ?_, ?_, ?_⟩
  all_goals
    first
    | solve | simp [Clause.ofList, Literal.conjugate]
    | apply LCS.Finset.ext
      intro L
      cases L with
      | pos k =>
        by_cases hR : k = R <;>
          simp_all [GCNF.Clause.union, GCNF.Clause.remove, Clause.ofList, Literal.conjugate]
      | neg k =>
        by_cases hR : k = R <;>
          simp_all [GCNF.Clause.union, GCNF.Clause.remove, Clause.ofList, Literal.conjugate]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D6_wellFormed := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  (ex436D6_allRowsWellFormed R ).wellFormed

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D6_counts := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    constructor <;> rfl

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D6_rootLabel := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  rfl

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

helper theorem Completeness.ex436D7_allRowsWellFormed (P Q R : Nat) (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    (ex436D7 P Q R).AllRowsWellFormed := by
  refine ⟨by simp [ex436D7], ?_⟩
  intro i n hn r hr
  have hi : i < 7 := by
    have := (List.getElem?_eq_some_iff.mp hn).1
    simpa [FiniteGraph.node, ex436D7] using this
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [FiniteGraph.node, ex436D7, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.some.injEq] at hn
  all_goals subst n
  all_goals cases hr
  all_goals refine ⟨by simp, by simp, _, _, rfl, rfl, ?_, ?_, ?_⟩
  all_goals
    first
    | solve | simp [Clause.ofList, Literal.conjugate]
    | apply LCS.Finset.ext
      intro L
      cases L with
      | pos k =>
        by_cases hP : k = P <;> by_cases hQ : k = Q <;> by_cases hR : k = R <;>
          simp_all [GCNF.Clause.union, GCNF.Clause.remove, Clause.ofList, Literal.conjugate]
      | neg k =>
        by_cases hP : k = P <;> by_cases hQ : k = Q <;> by_cases hR : k = R <;>
          simp_all [GCNF.Clause.union, GCNF.Clause.remove, Clause.ofList, Literal.conjugate]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D7_wellFormed := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  (ex436D7_allRowsWellFormed P Q R hPQ hPR hQR).wellFormed

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D7_counts := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    constructor <;> rfl

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D7_rootLabel := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  rfl

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

helper theorem Completeness.ex436D8_allRowsWellFormed (P Q R : Nat) (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R) :
    (ex436D8 P Q R).AllRowsWellFormed := by
  refine ⟨by simp [ex436D8], ?_⟩
  intro i n hn r hr
  have hi : i < 7 := by
    have := (List.getElem?_eq_some_iff.mp hn).1
    simpa [FiniteGraph.node, ex436D8] using this
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [FiniteGraph.node, ex436D8, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.some.injEq] at hn
  all_goals subst n
  all_goals cases hr
  all_goals refine ⟨by simp, by simp, _, _, rfl, rfl, ?_, ?_, ?_⟩
  all_goals
    first
    | solve | simp [Clause.ofList, Literal.conjugate]
    | apply LCS.Finset.ext
      intro L
      cases L with
      | pos k =>
        by_cases hP : k = P <;> by_cases hQ : k = Q <;> by_cases hR : k = R <;>
          simp_all [GCNF.Clause.union, GCNF.Clause.remove, Clause.ofList, Literal.conjugate]
      | neg k =>
        by_cases hP : k = P <;> by_cases hQ : k = Q <;> by_cases hR : k = R <;>
          simp_all [GCNF.Clause.union, GCNF.Clause.remove, Clause.ofList, Literal.conjugate]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D8_wellFormed := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  (ex436D8_allRowsWellFormed P Q R hPQ hPR hQR).wellFormed

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D8_counts := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    constructor <;> rfl

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D8_rootLabel := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  rfl

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex435D1_leavesFrom := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    intro i hi
    have hids : (ex435D1 P).leafIds = [0, 1] := rfl
    rw [hids] at hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl
    all_goals refine ⟨_, rfl, ?_⟩
    all_goals simp [ClauseSequent.ofList]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex435D2_leavesFrom := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    intro i hi
    have hids : (ex435D2 S).leafIds = [0, 1] := rfl
    rw [hids] at hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl
    all_goals refine ⟨_, rfl, ?_⟩
    all_goals simp [ClauseSequent.ofList]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex435D3_leavesFrom := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    intro i hi
    have hids : (ex435D3 P S).leafIds = [0, 1] := rfl
    rw [hids] at hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl
    all_goals refine ⟨_, rfl, ?_⟩
    all_goals simp [ClauseSequent.ofList]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex435D4_leavesFrom := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    intro i hi
    have hids : (ex435D4 P S).leafIds = [0, 1, 2] := rfl
    rw [hids] at hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl
    all_goals refine ⟨_, rfl, ?_⟩
    all_goals simp [ClauseSequent.ofList]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex435D5_leavesFrom := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    intro i hi
    have hids : (ex435D5 Q).leafIds = [0, 1] := rfl
    rw [hids] at hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl
    all_goals refine ⟨_, rfl, ?_⟩
    all_goals simp [ClauseSequent.ofList]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex435D6_leavesFrom := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    intro i hi
    have hids : (ex435D6 P Q S).leafIds = [0, 1, 2] := rfl
    rw [hids] at hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl
    all_goals refine ⟨_, rfl, ?_⟩
    all_goals simp [ClauseSequent.ofList]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex435D7_leavesFrom := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    intro i hi
    have hids : (ex435D7 P Q S).leafIds = [0, 1, 2, 3] := rfl
    rw [hids] at hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals refine ⟨_, rfl, ?_⟩
    all_goals simp [ClauseSequent.ofList]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D1_leavesFrom := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    intro i hi
    have hids : (ex436D1 P).leafIds = [0, 1] := rfl
    rw [hids] at hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl
    all_goals refine ⟨_, rfl, ?_⟩
    all_goals simp [ClauseSequent.ofList]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D2_leavesFrom := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    intro i hi
    have hids : (ex436D2 Q).leafIds = [0, 1] := rfl
    rw [hids] at hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl
    all_goals refine ⟨_, rfl, ?_⟩
    all_goals simp [ClauseSequent.ofList]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D3_leavesFrom := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    intro i hi
    have hids : (ex436D3 P Q).leafIds = [0, 1] := rfl
    rw [hids] at hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl
    all_goals refine ⟨_, rfl, ?_⟩
    all_goals simp [ClauseSequent.ofList]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D4_leavesFrom := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    intro i hi
    have hids : (ex436D4 P Q).leafIds = [0, 1, 2] := rfl
    rw [hids] at hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl
    all_goals refine ⟨_, rfl, ?_⟩
    all_goals simp [ClauseSequent.ofList]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D5_leavesFrom := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    intro i hi
    have hids : (ex436D5 P Q R).leafIds = [0, 1, 2] := rfl
    rw [hids] at hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl
    all_goals refine ⟨_, rfl, ?_⟩
    all_goals simp [ClauseSequent.ofList]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D6_leavesFrom := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    intro i hi
    have hids : (ex436D6 R).leafIds = [0, 1] := rfl
    rw [hids] at hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl
    all_goals refine ⟨_, rfl, ?_⟩
    all_goals simp [ClauseSequent.ofList]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D7_leavesFrom := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    intro i hi
    have hids : (ex436D7 P Q R).leafIds = [0, 1, 2, 3] := rfl
    rw [hids] at hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals refine ⟨_, rfl, ?_⟩
    all_goals simp [ClauseSequent.ofList]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D8_leavesFrom := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    intro i hi
    have hids : (ex436D8 P Q R).leafIds = [0, 1, 2, 3] := rfl
    rw [hids] at hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals refine ⟨_, rfl, ?_⟩
    all_goals simp [ClauseSequent.ofList]

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex435D7_isRefutationFor := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    refine ⟨ex435D7_wellFormed P Q S hPQ hPS hQS, ?_, rfl⟩
    have hleaves := ex435D7_leavesFrom P Q S
    intro i hi
    obtain ⟨C, hC, hmem⟩ := hleaves i hi
    refine ⟨C, hC, ?_⟩
    simpa [ex435Sequent, Clause.single_eq_ofList_singleton, ClauseSequent.ofList,
      or_assoc, or_left_comm, or_comm] using hmem

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D8_isRefutationFor := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    refine ⟨ex436D8_wellFormed P Q R hPQ hPR hQR, ?_, rfl⟩
    have hleaves := ex436D8_leavesFrom P Q R
    intro i hi
    obtain ⟨C, hC, hmem⟩ := hleaves i hi
    refine ⟨C, hC, ?_⟩
    simpa [ex436Sequent, Clause.single_eq_ofList_singleton, ClauseSequent.ofList,
      or_assoc, or_left_comm, or_comm] using hmem

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex435D3_alias_not_wellFormed := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    intro h
    have hrow := h.2.2 2 (LCS.Resolution.Method.FiniteGraph.root_mem_vertexIds _ h)
      ⟨Clause.ofList [.neg P], some ⟨.pos P, 0, 1⟩⟩ rfl
      ⟨.pos P, 0, 1⟩ rfl
    obtain ⟨a, b, ha, hb, _, _, he⟩ := hrow
    simp only [FiniteGraph.node, ex435D3, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at ha hb
    subst a; subst b
    have hm : Literal.neg P ∈ Clause.ofList [.neg P] := by simp [Clause.ofList]
    dsimp only at he
    rw [he] at hm
    simp [GCNF.Clause.union, GCNF.Clause.remove, Clause.ofList, Literal.conjugate] at hm

end LCS.Resolution.Method.Completeness
end
end

section
section
namespace LCS.Resolution.Method.Completeness
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.GCNF
open LCS.Resolution.GCNF
open LCS.Resolution.Method

proof_of ex436D5_alias_not_wellFormed := open LCS.Resolution.Method.Completeness.Proofs.Completeness in
  by
    intro h
    have hrow := h.2.2 4 (LCS.Resolution.Method.FiniteGraph.root_mem_vertexIds _ h)
      ⟨Clause.ofList [.pos Q], some ⟨.pos Q, 3, 2⟩⟩ rfl
      ⟨.pos Q, 3, 2⟩ rfl
    obtain ⟨a, b, ha, hb, _, _, he⟩ := hrow
    simp only [FiniteGraph.node, ex436D5, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at ha hb
    subst a; subst b
    have hm : Literal.pos Q ∈ Clause.ofList [.pos Q] := by simp [Clause.ofList]
    dsimp only at he
    rw [he] at hm
    simp [GCNF.Clause.union, GCNF.Clause.remove, Clause.ofList, Literal.conjugate] at hm

end LCS.Resolution.Method.Completeness
end
end
