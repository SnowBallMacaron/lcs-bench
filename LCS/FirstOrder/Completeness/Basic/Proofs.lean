import LCS.FirstOrder.Completeness.Basic

namespace LCS.FirstOrder.Completeness

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Gentzen.SignedFormulae

open LCS.FirstOrder.Gentzen.Hintikka







helper /-- Theorem 5.5.1 (companion): Textbook-faithful halt predicate. The
search procedure halts on input `seq` iff the concrete SearchTreeData
produced by `buildSearchTree seq hFree hCross hNoEq` has a finite tree
domain AND every leaf of that tree is either an axiom OR a finished
leaf with respect to the concrete `nodeState` at that leaf's address.

Contrast with `searchHalts` (infrastructure): that predicate uses an
abstract `∃ st : SearchState L, ...` which any record of the right
shape can witness, including mock ones. This concrete version threads
through the `buildSearchTree` construction, so producing the witness
requires actually exhibiting a finite tree with all leaves closed/
finished under the node's own state — the textbook's "search halts
with a closed tree T" claim. -/
noncomputable def searchHaltsConcrete {L : Language} [Countable (Term L)]
    (seq : Sequent L) (hFree : noFreeBound seq)
    (hCross : crossNoFreeBound seq) (hNoEq : seqNoEq seq) : Prop :=
  let w := buildSearchTree seq hFree hCross hNoEq
  w.treeDom.IsFinite ∧
  ∀ (addr : TreeAddr) (hu : addr ∈ w.treeDom.dom),
    ¬ ((addr ++ [0]) ∈ w.treeDom.dom) →
    isAxiom (w.nodeSequent addr hu) ∨
      Hintikka.SearchState.isFinishedLeaf (w.nodeState addr hu) (w.nodeSequent addr hu)

helper /-- Example 5.5.2: After exists:left on exists y Q(y), NUMACT goes from 0
to 1, activating y1 as eigenvariable. Represented as the pair (before, after) of NUMACT values. -/
def exEigenvariableActivation : Nat × Nat :=
  (0, 1)

proof_of exCounterDomainH_const := ⟨_, 0, Or.inl rfl, rfl⟩


proof_of exCounterDomainH_y1 := ⟨_, 0, Or.inr (Or.inl rfl), rfl⟩


proof_of exCounterDomainH_y2 := ⟨_, 0, Or.inr (Or.inr rfl), rfl⟩


proof_of exCounterDomainH_func := by
  obtain ⟨base, n, hb, rfl⟩ := ht
  exact ⟨base, n + 1, hb, rfl⟩


helper /-- Example 5.5.3: The structure on H falsifies A under every assignment:
y₂ witnesses ∃x P(x), Q(a) holds, and f(y₁) refutes ∀y P(f(y)). -/
theorem exCounterInterp_not_formula (as : Assignment exCounterInterp) :
    ¬ formulaEvalN exCounterInterp exFormulaPQa as := by
  intro h
  simp only [exFormulaPQa, formulaEvalN, LCS.FirstOrder.Basic.implM, LCS.FirstOrder.Basic.andM, termEval] at h
  have hf := h ⟨⟨⟨Term.var 5, exCounterDomainH_y2⟩, rfl⟩, rfl⟩
    ⟨Term.var 3, exCounterDomainH_y1⟩
  change Term.func (L := exLangPQa) ExFuncFa.f _ = Term.var 5 at hf
  cases hf

helper /-- Example 5.5.3: The structure on H falsifies the initial sequent → A. -/
theorem exCounterInterp_falsifies :
    sequentFalsifiableIn exCounterInterp (Sequent.mk [] [exFormulaPQa]) := by
  refine ⟨fun _ => ⟨Term.const ExConstA.a, exCounterDomainH_const⟩, ?_, ?_⟩
  · intro A h; cases h
  · intro B h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst B
    exact exCounterInterp_not_formula _

proof_of exCounterInterpWith_falsifies := by
  have hn : ¬ formulaEvalN (exCounterInterpWith p q) exFormulaPQa as := by
    intro h
    simp only [exFormulaPQa, formulaEvalN, LCS.FirstOrder.Basic.implM,
      LCS.FirstOrder.Basic.andM, termEval] at h
    exact hPf (h ⟨⟨⟨Term.var 5, exCounterDomainH_y2⟩, hP⟩, hQ⟩
      ⟨Term.var 3, exCounterDomainH_y1⟩)
  refine ⟨hn, as, ?_, ?_⟩
  · intro A h; cases h
  · intro B h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst B
    exact hn


helper /-- Finite embedding preserves falsifiability. -/
theorem infSequentFalsifiable_ofSequent_iff {L : Language} (s : Sequent L) :
    infSequentFalsifiable (InfSequentN.ofSequent s) ↔ sequentFalsifiable s := by
  simp only [infSequentFalsifiable, sequentFalsifiable,
    InfSequentN.memAntecedent_ofSequent, InfSequentN.memSuccedent_ofSequent]

end LCS.FirstOrder.Completeness
