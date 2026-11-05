import LCS.FirstOrder.Completeness.Search.Part1

section

namespace LCS.FirstOrder.Completeness.Search

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

helper /-- The x variables are pairwise distinct. -/
theorem Completeness.Search.xVar_injective {L : Language} : Function.Injective (xVar (L := L)) := by
  intro i j h
  have heq : 2 * i = 2 * j := Term.var.inj h
  omega

helper /-- The y variables are pairwise distinct. -/
theorem Completeness.Search.yVar_injective {L : Language} : Function.Injective (yVar (L := L)) := by
  intro i j h
  have heq : 2 * i + 1 = 2 * j + 1 := Term.var.inj h
  omega

helper /-- The input and reserved variable supplies are disjoint. -/
theorem Completeness.Search.xVar_ne_yVar {L : Language} (i j : Nat) : xVar (L := L) i ≠ yVar j := by
  intro h
  have heq : 2 * i = 2 * j + 1 := Term.var.inj h
  omega

helper /-- Every variable index belongs to one of the two supplies. -/
theorem Completeness.Search.variableIndex_partition (n : Nat) :
    (∃ i, n = 2 * i) ∨ (∃ i, n = 2 * i + 1) := by
  by_cases h : n % 2 = 0
  · exact Or.inl ⟨n / 2, by omega⟩
  · exact Or.inr ⟨n / 2, by omega⟩

helper /-- Even-index renaming sends an input variable to xᵢ. -/
theorem Completeness.Search.evenTerm_var {L : Language} (i : Nat) :
    InfiniteSearch.evenTerm (L := L) (.var i) = xVar i := rfl



end LCS.FirstOrder.Completeness.Search

end

section

namespace LCS.FirstOrder.SyntaxN.FormulaN

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.Completeness

open LCS.FirstOrder.Completeness.Search



helper /-- Reserved y variables occur neither free nor bound in an x-built formula. -/
theorem SyntaxN.FormulaN.builtFromX_y_fresh {L : Language} {A : FormulaN L}
    (hA : A.builtFromX) (i : Nat) :
    2 * i + 1 ∉ formulaFVN A ∧ 2 * i + 1 ∉ formulaBVN A := by
  constructor
  · intro h
    have heven := hA _ (Or.inl h)
    simp [isXIndex] at heven
  · intro h
    have heven := hA _ (Or.inr h)
    simp [isXIndex] at heven

end LCS.FirstOrder.SyntaxN.FormulaN

end

section

namespace LCS.FirstOrder.Completeness.Search

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Gentzen.SignedFormulae

helper /-- The initial zero-th availability stream is the tail of TERMS. -/
theorem Completeness.Search.initialTermState_avail_zero {L : Language} (hL : L.withoutEquality)
    (q : InfSequentN L) (hq : q.builtFromX) (terms : TermsEnum q)
    (avail : ∀ i, 0 < i → AvailEnum q i) :
    (initialTermState hL q hq terms avail).avail 0 = terms.toTermStream.tail := rfl

helper /-- Every positive availability stream starts at its designated reserved variable. -/
theorem Completeness.Search.initialTermState_avail_succ_head {L : Language} (hL : L.withoutEquality)
    (q : InfSequentN L) (hq : q.builtFromX) (terms : TermsEnum q)
    (avail : ∀ i, 0 < i → AvailEnum q i) (j : Nat) :
    ((initialTermState hL q hq terms avail).avail (j + 1)).head = some (yVar (j + 1)) :=
  (avail (j + 1) (by omega)).starts_with

helper /-- Exhausted streams add no initial term record. -/
theorem Completeness.Search.initialTermRecords_empty {L : Language} :
    initialTermRecords (TermStream.empty L) = [] := rfl

helper /-- In the generator-free case the initial root record is exactly ⟨y₀, nil⟩. -/
theorem Completeness.Search.initialTermRecords_fallback {L : Language} {q : InfSequentN L}
    (terms : TermsEnum q) (h : ¬ hasInputGenerators q) :
    initialTermRecords terms.toTermStream = [(yVar 0, [])] := by
  unfold initialTermRecords TermStream.head
  rw [terms.fallback_head h]

end LCS.FirstOrder.Completeness.Search

end

section

namespace LCS.FirstOrder.Completeness.Search

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.Gentzen









end LCS.FirstOrder.Completeness.Search

end
