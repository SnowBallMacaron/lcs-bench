import LCS.FirstOrder.Equality.Search.Part1

section

namespace LCS.FirstOrder.Equality.Search

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.Gentzen LCS.FirstOrder.Gentzen.SignedFormulae

open LCS.FirstOrder.Completeness.Search

helper /-- Definition 5.6.3: A nonempty packet is a single generalized-equality inference. -/
def Search.equalityPacket_inference {L : Language} (hL : L.hasEquality = true)
    (s : Sequent L) (heads : List (EqEntry L)) (hne : heads ≠ [])
    (proof : GEqProofTree hL (appendHeads s heads)) : GEqProofTree hL s := by
  apply GEqProofTree.eqGeneral (heads.map Subtype.val) (by
    intro h
    cases heads with
    | nil => exact hne rfl
    | cons e es => cases h)
    (fun A hA => ?_) s.antecedent s.succedent proof
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hA
  exact e.property hL

helper /-- An exhausted next stream cannot activate a variable. -/
theorem Search.activateVariable_of_empty {L : Language} (hL : L.hasEquality = true)
    {root : Sequent L} (kind : EigenRuleKind) (x : Nat) (A : FormulaN L)
    (st : SearchState L root) (h : (st.avail (st.numact + 1)).head = none) :
    activateVariable hL kind x A st = st := by
  simp [activateVariable, h]

helper /-- If no leaf admits the rule, all global and branch bookkeeping is unchanged. -/
theorem Search.activateVariable_of_no_application {L : Language} (hL : L.hasEquality = true)
    {root : Sequent L} (kind : EigenRuleKind) (x : Nat) (A : FormulaN L)
    (st : SearchState L root) (y : Nat)
    (hhead : (st.avail (st.numact + 1)).head = some (.var y))
    (hstep : (activateTree hL kind x A y st.tree).2 = false) :
    activateVariable hL kind x A st = st := by
  simp [activateVariable, hhead, hstep]

helper /-- Availability streams above NUMACT are unchanged by round-end transfer. -/
theorem Search.roundEndUpdate_avail_above {L : Language} {root : Sequent L}
    (st : SearchState L root) (i : Nat) (hi : st.numact < i) :
    (roundEndUpdate st).avail i = st.avail i := by
  simp [roundEndUpdate, Nat.not_le.mpr hi]

helper /-- Each active stream is tailed exactly once at round end. -/
theorem Search.roundEndUpdate_avail_active {L : Language} {root : Sequent L}
    (st : SearchState L root) (i : Nat) (hi : i ≤ st.numact) :
    (roundEndUpdate st).avail i = (st.avail i).tail := by
  simp [roundEndUpdate, hi]

end LCS.FirstOrder.Equality.Search

end
