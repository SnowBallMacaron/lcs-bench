import LCS.Item
import LCS.Util
import LCS.SLD.LogicProgramming
import LCS.SLD.LogicProgramming.Correctness.SubstitutedClauseSet
import LCS.SLD.LogicProgramming.Correctness.CorrectnessTheorem
import LCS.SLD.LogicProgramming.Correctness.ExampleProgram
import LCS.SLD.LogicProgramming.Correctness.ExampleTeacherRefutations
import LCS.SLD.LogicProgramming.Correctness.ExampleRichRefutations
import LCS.SLD.LogicProgramming.Correctness.ExampleAnswers

/-! # SLD.LogicProgramming.Correctness (Section 9.5.3)
    Source: Logic for Computer Science, Gallier 2015

    Correctness of SLD-resolution as a computational procedure:
    Lemma 9.5.3 (unsatisfiability of substituted clause set),
    Theorem 9.5.1 (correctness of SLD-resolution), and
    Example 9.5.4 (four SLD-refutations for the logic program
    from Example 9.5.1).
-/
