import LCS.FirstOrder.Completeness.Search.Part2

section

namespace LCS.FirstOrder.Completeness.Search

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.Gentzen

helper /-- Definition 5.5.1: The union of finite search stages assigns a unique
label to each address. -/
theorem Search.searchLimit51_unique {L : Language} (hL : L.withoutEquality)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) (p : List Nat) (s t : Sequent L)
    (hs : searchLimit51 hL q hq hFB enum p s)
    (ht : searchLimit51 hL q hq hFB enum p t) : s = t := by
  obtain ⟨i, hi⟩ := hs
  obtain ⟨j, hj⟩ := ht
  have hi' := search51_labelAt_mono hL q hq hFB enum i j p s hi
  have hj' := search51_labelAt_mono hL q hq hFB enum j i p t hj
  rw [Nat.add_comm j i] at hj'
  rw [hi'] at hj'
  exact Option.some.inj hj'

helper /-- Definition 5.5.1: Every present head of an active AVAIL stream is
placed in TERM₀ by the round-end transfer, including AVAIL₀. -/
theorem Search.roundEndUpdate_head_mem {L : Language} {root : Sequent L}
    (st : SearchState L root) (i : Nat) (hi : i ≤ st.numact) (t : Term L)
    (ht : (st.avail i).head = some t) : t ∈ (roundEndUpdate st).TERM0 := by
  apply List.mem_append.mpr
  right
  exact List.mem_filterMap.mpr ⟨i, List.mem_range.mpr (Nat.lt_succ_of_le hi), ht⟩

end LCS.FirstOrder.Completeness.Search

end

section

namespace LCS.FirstOrder.Completeness.Search

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Gentzen.SignedFormulae

helper /-- TERMS admissibility factors exactly through the input's three symbol sets. -/
theorem Search.termsEnum_iff_admissibleOfSymbols {L : Language} (q : InfSequentN L)
    (stream : TermStream L) :
    (∃ e : TermsEnum q, e.toTermStream = stream) ↔
      TermsAdmissibleOfSymbols (signedSetFunSyms (inputSignedSet q))
        (signedSetConstSyms (inputSignedSet q)) (signedSetFreeVars (inputSignedSet q)) stream := by
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e.enumerates, e.fallback_head⟩
  · rintro ⟨he, hf⟩
    exact ⟨{ toTermStream := stream, enumerates := he, fallback_head := hf }, rfl⟩

helper /-- AVAIL admissibility factors exactly through the input's three symbol sets. -/
theorem Search.availEnum_iff_admissibleOfSymbols {L : Language} (q : InfSequentN L)
    (i : Nat) (stream : TermStream L) :
    (∃ e : AvailEnum q i, e.toTermStream = stream) ↔
      AvailAdmissibleOfSymbols (signedSetFunSyms (inputSignedSet q))
        (signedSetConstSyms (inputSignedSet q)) (signedSetFreeVars (inputSignedSet q)) i stream := by
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e.index_pos, e.enumerates, e.starts_with⟩
  · rintro ⟨hi, he, hh⟩
    exact ⟨{ toTermStream := stream, index_pos := hi, enumerates := he, starts_with := hh }, rfl⟩

proof_of exists_renaming_crossNoFreeBoundInf := by
  -- REPAIR(T170): proof pending
  sorry

end LCS.FirstOrder.Completeness.Search

end

section

namespace LCS.FirstOrder.Completeness

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.Completeness.Search

proof_of exAFG_admissible_prefixes := by
  -- REPAIR(T102): proof pending
  sorry


end LCS.FirstOrder.Completeness

end

section

namespace LCS.FirstOrder.Completeness

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.Gentzen LCS.FirstOrder.Gentzen.Hintikka

open LCS.FirstOrder.Completeness.Search LCS.FirstOrder.Completeness.InfiniteSearch

proof_of exProofTreeClosureFuncSyms := by
  -- REPAIR(T103): proof pending
  sorry


end LCS.FirstOrder.Completeness

end

section

namespace LCS.FirstOrder.Completeness

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.Gentzen LCS.FirstOrder.Gentzen.Hintikka

open LCS.FirstOrder.Completeness.Search LCS.FirstOrder.Completeness.InfiniteSearch

proof_of exSearchCounterFuncSyms_trace := by
  -- REPAIR(T104): proof pending
  sorry


end LCS.FirstOrder.Completeness

end
