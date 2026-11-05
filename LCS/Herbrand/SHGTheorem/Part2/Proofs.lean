import LCS.Herbrand.SHGTheorem.Part2

section

namespace LCS.Herbrand.SHGTheorem

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.Herbrand.NNFHauptsatz

open LCS.Herbrand.HerbrandTheorem

namespace SkolemAllocationRegression

helper def SkolemAllocationRegression.duplicateSource : FormulaN language :=
  .conj oneSource oneSource

helper def SkolemAllocationRegression.nestedInner : FormulaN language :=
  .ex 3 (atom .p)

helper def SkolemAllocationRegression.siblingIndex0 : Fin siblingSpec.n := ⟨0, by decide⟩

helper def SkolemAllocationRegression.siblingIndex1 : Fin siblingSpec.n := ⟨1, by decide⟩

helper def SkolemAllocationRegression.nestedIndex0 : Fin nestedSpec.n := ⟨0, by decide⟩



helper /-- The old over-allocation value is definitionally excluded. -/
theorem SkolemAllocationRegression.zero_not_overallocated : zeroSpec.n ≠ 1 := by decide

helper /-- One existential allocates exactly one symbol. -/
theorem SkolemAllocationRegression.one_exact : oneSpec.n = 1 := by rfl

helper /-- The sole allocation is the sole existential occurrence with empty scope. -/
theorem SkolemAllocationRegression.one_allocation_exact :
    oneSpec.allocation oneIndex = (oneSource, []) := by rfl

helper theorem SkolemAllocationRegression.one_scope_exact : oneSpec.skolemScope oneIndex = [] := by rfl

helper theorem SkolemAllocationRegression.one_rank_exact : oneSpec.skolemRank oneIndex = 0 := by rfl

helper /-- Old under- and over-allocation values are both excluded. -/
theorem SkolemAllocationRegression.one_not_underallocated : oneSpec.n ≠ 0 := by decide

helper theorem SkolemAllocationRegression.one_not_overallocated : oneSpec.n ≠ 2 := by decide

helper /-- Filtering preserves two structurally identical existential cells
as two preorder occurrences. -/
theorem SkolemAllocationRegression.duplicate_syntax_preserves_multiplicity :
    _root_.LCS.Herbrand.SHGTheorem.existentialDescriptors duplicateSource =
      [(oneSource, []), (oneSource, [])] := by rfl

helper /-- Sibling existentials under one universal have equal rank while
retaining their left-to-right occurrence order. -/
theorem SkolemAllocationRegression.sibling_allocations_exact :
    siblingSpec.allocations =
      [(siblingLeft, [0]), (siblingRight, [0])] := by rfl

helper theorem SkolemAllocationRegression.sibling_count_exact : siblingSpec.n = 2 := by rfl

helper theorem SkolemAllocationRegression.sibling_left_exact :
    siblingSpec.allocation siblingIndex0 = (siblingLeft, [0]) := by rfl

helper theorem SkolemAllocationRegression.sibling_right_exact :
    siblingSpec.allocation siblingIndex1 = (siblingRight, [0]) := by rfl

helper theorem SkolemAllocationRegression.sibling_equal_ranks :
    siblingSpec.skolemRank siblingIndex0 = 1 ∧
      siblingSpec.skolemRank siblingIndex1 = 1 := by
  exact ⟨rfl, rfl⟩

helper /-- Equal ranks do not identify symbols: occurrence positions remain
distinct indices in the Skolem language. -/
theorem SkolemAllocationRegression.sibling_symbols_distinct :
    (Sum.inr ⟨siblingIndex0, by decide⟩ : siblingSpec.language.funSymbols) ≠
      Sum.inr ⟨siblingIndex1, by decide⟩ := by
  simp [siblingIndex0, siblingIndex1]

helper /-- Nested existential scopes and ranks follow exact preorder. -/
theorem SkolemAllocationRegression.nested_allocations_exact :
    nestedSpec.allocations =
      [(nestedOuter, [0]), (nestedInner, [0, 2])] := by rfl

helper theorem SkolemAllocationRegression.nested_count_exact : nestedSpec.n = 2 := by rfl

helper theorem SkolemAllocationRegression.nested_outer_exact :
    nestedSpec.allocation nestedIndex0 = (nestedOuter, [0]) := by rfl

helper theorem SkolemAllocationRegression.nested_inner_exact :
    nestedSpec.allocation nestedIndex1 = (nestedInner, [0, 2]) := by rfl

helper theorem SkolemAllocationRegression.nested_rank_order_exact :
    nestedSpec.skolemRank nestedIndex0 = 1 ∧
      nestedSpec.skolemRank nestedIndex1 = 2 := by
  exact ⟨rfl, rfl⟩

helper /-- The old reordered rank assignment is impossible at both positions. -/
theorem SkolemAllocationRegression.nested_reordered_ranks_rejected :
    nestedSpec.skolemRank nestedIndex0 ≠ 2 ∧
      nestedSpec.skolemRank nestedIndex1 ≠ 1 := by
  decide

end SkolemAllocationRegression

end LCS.Herbrand.SHGTheorem

end

section

namespace LCS.Herbrand.SHGTheorem

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.Herbrand.NNFHauptsatz

open LCS.Herbrand.HerbrandTheorem







helper /-- Top-level traversal consumes all and only the computed
allocations. -/
theorem skolemFormTraversal_counter {L : Language}
    (S : SkolemSpec L) :
    (skolemFormTraversal S).2 = S.n := by
  obtain ⟨B, hB⟩ := skolemFormExactAux_top_result S
  have hGet :
      skolemFormTraversal S = (B, S.n) :=
    Option.get_of_eq_some (skolemFormExactAux_top_isSome S) hB
  exact congrArg Prod.snd hGet





end LCS.Herbrand.SHGTheorem

end

section

namespace LCS.Herbrand.SHGTheorem

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.Herbrand.NNFHauptsatz

open LCS.Herbrand.HerbrandTheorem

namespace SkolemAllocationRegression

helper /-- The zero-existential traversal consumes no allocation. -/
theorem SkolemAllocationRegression.zero_traversal_consumes_all :
    (_root_.LCS.Herbrand.SHGTheorem.skolemFormTraversal zeroSpec).2 = 0 := by
  rw [skolemFormTraversal_counter]
  exact zero_exact

helper /-- The single top-level existential consumes its sole rank-zero
allocation. -/
theorem SkolemAllocationRegression.one_traversal_consumes_all :
    (_root_.LCS.Herbrand.SHGTheorem.skolemFormTraversal oneSpec).2 = 1 := by
  rw [skolemFormTraversal_counter]
  exact one_exact

helper /-- A rank-zero allocation has no argument position, so its exact term
is a Skolem constant rather than an arbitrary-variable fallback. -/
theorem SkolemAllocationRegression.one_argument_domain_empty :
    Fin (oneSpec.skolemRank oneIndex) → False :=
  Fin.elim0

helper /-- Sibling allocations are both consumed in left-to-right order. -/
theorem SkolemAllocationRegression.sibling_traversal_consumes_all :
    (_root_.LCS.Herbrand.SHGTheorem.skolemFormTraversal siblingSpec).2 = 2 := by
  rw [skolemFormTraversal_counter]
  exact sibling_count_exact

helper theorem SkolemAllocationRegression.sibling_left_argument_exact :
    _root_.LCS.Herbrand.SHGTheorem.exactSkolemArgument siblingSpec siblingIndex0 ⟨0, by decide⟩ =
      Term.var 0 := by
  rfl

helper theorem SkolemAllocationRegression.sibling_right_argument_exact :
    _root_.LCS.Herbrand.SHGTheorem.exactSkolemArgument siblingSpec siblingIndex1 ⟨0, by decide⟩ =
      Term.var 0 := by
  rfl

helper /-- The nested traversal consumes both allocations, and the inner
symbol's ordered argument vector is exactly `[x₀, x₂]`. -/
theorem SkolemAllocationRegression.nested_traversal_consumes_all :
    (_root_.LCS.Herbrand.SHGTheorem.skolemFormTraversal nestedSpec).2 = 2 := by
  rw [skolemFormTraversal_counter]
  exact nested_count_exact

helper theorem SkolemAllocationRegression.nested_outer_argument_exact :
    _root_.LCS.Herbrand.SHGTheorem.exactSkolemArgument nestedSpec nestedIndex0 ⟨0, by decide⟩ =
      Term.var 0 := by
  rfl

helper theorem SkolemAllocationRegression.nested_inner_argument_zero_exact :
    _root_.LCS.Herbrand.SHGTheorem.exactSkolemArgument nestedSpec nestedIndex1 ⟨0, by decide⟩ =
      Term.var 0 := by
  rfl

helper theorem SkolemAllocationRegression.nested_inner_argument_one_exact :
    _root_.LCS.Herbrand.SHGTheorem.exactSkolemArgument nestedSpec nestedIndex1 ⟨1, by decide⟩ =
      Term.var 2 := by
  rfl

end SkolemAllocationRegression

end LCS.Herbrand.SHGTheorem

end
