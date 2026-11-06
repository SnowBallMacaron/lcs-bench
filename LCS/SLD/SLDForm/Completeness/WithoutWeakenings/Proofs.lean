import LCS.SLD.SLDForm.Completeness.WithoutWeakenings

section
namespace LCS.SLD.SLDForm.Completeness
open LCS.Resolution.GCNF
open LCS.SLD.SLDForm
open LCS.SLD.SLDForm.Occurrence

proof_of gcnf_proof_without_weakenings := by
  -- BEGIN PROOF
    obtain ⟨D, hLeaves⟩ :=
      gcnf_occurrence_proof_without_weakenings
        S hNe hProv
    exact
      ⟨D.compress hLeaves,
        isWithoutWeakenings_of_isUnaryOccurrenceCompression
          (D.compress hLeaves) (D.compress_isUnaryOccurrenceCompression hLeaves),
        D.compress_axiomsAllSingleLiteral hLeaves⟩

end LCS.SLD.SLDForm.Completeness
end
