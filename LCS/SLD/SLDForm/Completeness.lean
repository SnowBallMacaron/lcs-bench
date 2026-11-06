import LCS.Item
import LCS.Util
import LCS.SLD.SLDForm.Occurrence
import LCS.SLD.SLDForm.Completeness.Basics
import LCS.SLD.SLDForm.Completeness.WithoutWeakenings
import LCS.SLD.SLDForm.Completeness.PermutationLemma
import LCS.SLD.SLDForm.Completeness.AxiomLabeling
import LCS.SLD.SLDForm.Completeness.GoalReduction
import LCS.SLD.SLDForm.Completeness.Theorems

/-! # SLD.SLDForm.Completeness
    Formalization of Chapter 9, Sections 9.2.2-9.2.3.
    Completeness of GCNF'-proofs in SLD-form: permutation lemma,
    combinatorial properties, and the main completeness theorem.
    Source: Logic for Computer Science, Gallier 2015
-/
