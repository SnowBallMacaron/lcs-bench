import LCS.SLD.SLDForm

namespace LCS.SLD.SLDForm

open LCS.Resolution.GCNF

proof_of exSLDFormProof_isSLDForm := by
  exact isSLDFormB_sound exSLDFormProof.kernel exSLDFormProof_check

end LCS.SLD.SLDForm
