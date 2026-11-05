import LCS.Herbrand.PrimRecursive

namespace LCS.Herbrand.PrimRecursive

namespace minimize

helper /-- Definition 7.7.5 (companion theorem): The graph characterization of the
least zero, with strict definedness and nonzero values at every earlier index. -/
theorem minimize.graphIff (n : Nat) (g : PartialNaryFunc (n + 1))
    (args : Fin n → Nat) (y : Nat) :
    minimize n g args y ↔
      g (fun i => if h : i.val < n then args ⟨i.val, h⟩ else y) = some 0 ∧
      ∀ z, z < y → ∃ v,
        g (fun i => if h : i.val < n then args ⟨i.val, h⟩ else z) = some v ∧ v ≠ 0 :=
  Iff.rfl

helper /-- Definition 7.7.5 (companion theorem): The convergence graph has at most
one output for each input, so it represents a partial function. -/
theorem minimize.functional (n : Nat) (g : PartialNaryFunc (n + 1))
    (args : Fin n → Nat) {y z : Nat}
    (hy : minimize n g args y) (hz : minimize n g args z) : y = z := by
  by_cases h : y < z
  · obtain ⟨v, hv, hn⟩ := hz.2 y h
    have he : (some 0 : Option Nat) = some v := hy.1.symm.trans hv
    exact False.elim (hn (Option.some.inj he).symm)
  · by_cases h' : z < y
    · obtain ⟨v, hv, hn⟩ := hy.2 z h'
      have he : (some 0 : Option Nat) = some v := hz.1.symm.trans hv
      exact False.elim (hn (Option.some.inj he).symm)
    · omega

proof_of domainIff := open LCS.Herbrand.PrimRecursive.Proofs.minimize in
  by
    classical
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y, hy.1, ?_⟩
      intro z hz
      by_cases he : z = y
      · subst z
        exact ⟨0, hy.1⟩
      · obtain ⟨v, hv, _⟩ := hy.2 z (by omega)
        exact ⟨v, hv⟩
    · rintro ⟨y, hy, hp⟩
      induction y using Nat.strongRecOn with
      | ind y ih =>
        by_cases he : ∃ z, z < y ∧
            g (fun i => if h : i.val < n then args ⟨i.val, h⟩ else z) = some 0
        · obtain ⟨z, hz, hzero⟩ := he
          exact ih z hz hzero (fun k hk => hp k (by omega))
        · refine ⟨y, hy, ?_⟩
          intro z hz
          obtain ⟨v, hv⟩ := hp z (by omega)
          refine ⟨v, hv, ?_⟩
          intro hvzero
          exact he ⟨z, hz, hv.trans (congrArg some hvzero)⟩


end minimize

helper /-- The total binary input in the remark following Definition 7.7.6:
g(x,y) = x + y + 1, represented in the partial-function carrier by some.
The first coordinate is x and the final coordinate is the search variable y. -/
def minimizationPositiveInput : PartialNaryFunc 2 :=
  fun args => some (args 0 + args 1 + 1)

helper /-- The concrete input g(x,y) = x + y + 1 is defined at every binary input. -/
theorem minimizationPositiveInputTotal :
    ∀ args : Fin 2 → Nat, ∃ v, minimizationPositiveInput args = some v := by
  intro args
  exact ⟨args 0 + args 1 + 1, rfl⟩

helper /-- The strict unbounded minimum of g(x,y) = x + y + 1 is undefined for
every natural x: no candidate y can satisfy the required zero equation. -/
theorem minimizationPositiveInputNowhereDefined (x y : Nat) :
    ¬ minimize 1 minimizationPositiveInput (fun _ => x) y := by
  intro h
  have hz : x + y + 1 = 0 := Option.some.inj h.1
  omega

helper /-- Minimization does not preserve totality: the displayed total binary
input has a unary strict unbounded minimum which is not total. This is an
existential failure of preservation; composition and primitive recursion on
total functions retain their existing total-function result types. -/
theorem minimizationDoesNotPreserveTotality :
    ∃ g : PartialNaryFunc 2,
      (∀ args, ∃ v, g args = some v) ∧
      ¬ (∀ args : Fin 1 → Nat, ∃ y, minimize 1 g args y) := by
  refine ⟨minimizationPositiveInput, minimizationPositiveInputTotal, ?_⟩
  intro h
  obtain ⟨y, hy⟩ := h (fun _ => 0)
  exact minimizationPositiveInputNowhereDefined 0 y hy

helper /-- A problem A ⊆ Nat is decidable when one unary total-recursive program
has exactly its characteristic graph: value 1 on members and value 0 on
nonmembers. The same program handles every input; convergence has no fixed
fuel bound. This uses the convergence interpretation of Definition 7.7.6. -/
def decidableProblem (A : Set Nat) : Prop :=
  ∃ pr : PartialRec 1, pr.isTotal ∧
    ∀ n v, pr.converges (fun _ => n) v ↔
      (n ∈ A ∧ v = 1) ∨ (n ∉ A ∧ v = 0)

helper /-- A problem A ⊆ Nat is partially decidable when one unary partial-recursive
program returns exactly 1 on members. At each nonmember it either has no
convergent value or returns exactly 0. The alternative is chosen pointwise,
inside the input quantifier; no totality requirement is imposed. Equality of
the value graphs explicitly excludes every output other than the specified
one, and undefinedness means failure at every fuel, not a single timeout. -/
def partiallyDecidableProblem (A : Set Nat) : Prop :=
  ∃ pr : PartialRec 1, ∀ n,
    (n ∈ A → ∀ v, pr.converges (fun _ => n) v ↔ v = 1) ∧
    (n ∉ A →
      (∀ v, ¬ pr.converges (fun _ => n) v) ∨
      (∀ v, pr.converges (fun _ => n) v ↔ v = 0))

proof_of ackermannIsRecursive := by
  -- REPAIR(T7-114): proof pending
  sorry


proof_of ackermannNotPrimitiveRecursive := by
  -- REPAIR(T7-114): proof pending
  sorry


end LCS.Herbrand.PrimRecursive
