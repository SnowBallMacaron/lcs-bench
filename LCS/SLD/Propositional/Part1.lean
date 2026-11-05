import LCS.Item
import LCS.Util
import LCS.SLD.SLDForm
import LCS.SLD.SLDForm.Completeness
import LCS.Resolution.Method.FiniteGraph
import Attach
import LCS.SLD.Propositional.Part1.ProofsStamp

section
namespace LCS.SLD.Propositional
open LCS.Resolution.GCNF
open LCS.SLD.SLDForm

/-- Definition 9.3.2 (companion): Given a negative clause N_i and a
    definite clause C, checks that some negative literal neg A_k in N_i
    has a matching positive literal pos A_k in C.
    I.e., ∃ A, Literal.neg A ∈ N_i ∧ Literal.pos A ∈ C. -/
@[blueprint "chap9__definition_9_3_2"]
def selectedAtomMatches (Ni : Clause) (A : Nat) (C : Clause)
    : Prop :=
  Literal.neg A ∈ Ni ∧ Literal.pos A ∈ C

-- ========= Definition 9.3.2 (companion): resolveStep =========

/-- Definition 9.3.2 (companion): Given a negative clause
    N_i = {neg A_1,...,neg A_n}, a selected atom A_k, and a definite
    clause C = {neg B_1,...,neg B_m, pos A_k}, produce the next clause
    N_{i+1} = (N_i \ {neg A_k}) ∪ {neg B_j | neg B_j ∈ C}.
    This removes neg A_k from N_i and adds all negative literals from C. -/
@[blueprint "chap9__definition_9_3_2"]
def resolveStep (Ni : Clause) (A : Nat) (C : Clause)
    : Clause :=
  let niWithout := Clause.remove Ni (Literal.neg A)
  let cNeg : Clause := Finset.filter (fun l => match l with
    | Literal.neg _ => true
    | Literal.pos _ => false) C
  Clause.union niWithout cNeg

-- ========= Definition 9.3.2: SLDDerivation =========

/-- The ordered choice made at one resolution transition. Equal side clauses
may be used at several different indices; each use retains its selected atom. -/
@[blueprint "chap9__definition_9_3_2"]
structure SLDStepWitness where
  selectedAtom : Nat
  sideClause : Clause

/-- Definition 9.3.2: A finite nonempty trace of negative clauses over an
arbitrary definite program and a finite family of negative input goals.
Every transition validates its stored selected atom and original side input.
Negative clauses may be empty, including the initial and final goal. -/
@[blueprint "chap9__definition_9_3_2" (main := true)]
structure SLDDerivation where
  definiteClauses : Set Clause
  definiteValid : ∀ C ∈ definiteClauses, isDefiniteClause C
  goals : List Clause
  goalsNegative : ∀ C ∈ goals, allNegative C
  sequence : List Clause
  sequenceNegative : ∀ C ∈ sequence, allNegative C
  seqNonempty : sequence ≠ []
  initialIsGoal : sequence.head seqNonempty ∈ goals
  steps : Fin (sequence.length - 1) → SLDStepWitness
  stepValid : ∀ i : Fin (sequence.length - 1),
    (steps i).sideClause ∈ definiteClauses ∧
    selectedAtomMatches (sequence.get ⟨i.val, by omega⟩)
      (steps i).selectedAtom (steps i).sideClause ∧
    sequence.get ⟨i.val + 1, by omega⟩ =
      resolveStep (sequence.get ⟨i.val, by omega⟩)
        (steps i).selectedAtom (steps i).sideClause

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Ordered selected atoms of the actual stored transitions. -/
def SLDDerivation.selectedAtoms (d : SLDDerivation) : List Nat :=
  List.ofFn (fun i => (d.steps i).selectedAtom)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The initial goal followed by every original side-clause use, in order.
Repeated uses are retained; transition i supplies input position i+1. -/
def SLDDerivation.inputClauses (d : SLDDerivation) : List Clause :=
  d.sequence.head d.seqNonempty :: List.ofFn (fun i => (d.steps i).sideClause)

-- ========= Definition 9.3.2 (companion): isSLDRefutation =========

/-- Definition 9.3.2 (companion): An SLD-derivation is an SLD-refutation
    iff the last clause in the sequence is the empty clause. -/
@[blueprint "chap9__definition_9_3_2"]
def isSLDRefutation (d : SLDDerivation) : Prop :=
  d.sequence.getLast d.seqNonempty = Clause.empty

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The ordered original side-clause uses of the stored transitions.
Repeated uses of the same clause retain their separate list positions. -/
@[blueprint "chap9__definition_9_3_2"]
def SLDDerivation.inputUses (d : SLDDerivation) : List Clause :=
  List.ofFn (fun i => (d.steps i).sideClause)

-- ATTACH-KEEP: rewrite uses the defining module's generated filter matcher
-- ATTACH-BLOCKER: rewrite uses the defining module's generated filter matcher
/-- Definite-clause filtering is exactly positive-pivot deletion. -/
theorem resolveStep_isResolvent (N C : Clause) (P : Nat)
    (hDef : isDefiniteClause C) (hMatch : selectedAtomMatches N P C) :
    LCS.Resolution.Method.Clause.isResolvent (resolveStep N P C) N C := by
  have hBody : Finset.filter (fun l => match l with
      | Literal.neg _ => true | Literal.pos _ => false) C = Clause.remove C (.pos P) := by
    apply Finset.ext; intro l
    change _ ↔ l ∈ Finset.erase C (.pos P)
    rw [Finset.mem_filter, Finset.mem_erase]
    cases l with
    | neg Q => simp
    | pos Q =>
      constructor
      · rintro ⟨_, h⟩; cases h
      · rintro ⟨hQ, hNe⟩
        have hEq := hDef.1.2 Q P hQ hMatch.2
        exact False.elim (hNe (congrArg Literal.pos hEq))
  refine ⟨Literal.neg P, hMatch.1, hMatch.2, ?_⟩
  change Clause.union (Clause.remove N (.neg P)) _ =
    Clause.union (Clause.remove N (.neg P)) (Clause.remove C (.pos P))
  rw [hBody]

/-- Each actual transition resolves the preceding negative clause with its
recorded original side input. The finite input-use list is the same record
used by the derivation and graph, rather than a new existential choice. -/
@[blueprint "chap9__definition_9_3_2"]
theorem sldDerivation_isLinearInput (d : SLDDerivation) :
    d.inputUses.length = d.sequence.length - 1 ∧
    ∀ i : Fin (d.sequence.length - 1),
      d.inputUses.get ⟨i.val, by simp [SLDDerivation.inputUses]⟩ =
        (d.steps i).sideClause ∧
      (d.steps i).sideClause ∈ d.definiteClauses ∧
      LCS.Resolution.Method.Clause.isResolvent
        (d.sequence.get ⟨i.val + 1, by omega⟩)
        (d.sequence.get ⟨i.val, by omega⟩) (d.steps i).sideClause 

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- A concrete finite node table for the derivation. Spine occurrence N_i has
ID 2*i, side use C_i has ID 2*i+1, and N_(i+1) records exactly those two
premises and the stored negative pivot. Equal labels never merge IDs. -/
@[blueprint "chap9__definition_9_3_2"]
def SLDDerivation.resolutionGraph (d : SLDDerivation) : LCS.Resolution.Method.FiniteGraph where
  table := List.ofFn fun i : Fin (2 * d.sequence.length - 1) =>
    if hEven : i.val % 2 = 0 then
      { clause := d.sequence.get ⟨i.val / 2, by have := i.isLt; omega⟩
        inference := if hZero : i.val = 0 then none else
          let k : Fin (d.sequence.length - 1) := ⟨i.val / 2 - 1, by have := i.isLt; omega⟩
          some { pivot := Literal.neg (d.steps k).selectedAtom
                 left := 2 * k.val
                 right := 2 * k.val + 1 } }
    else
      { clause := (d.steps ⟨i.val / 2, by have := i.isLt; omega⟩).sideClause
        inference := none }
  root := 2 * (d.sequence.length - 1)

/-- The actual finite table realizes the displayed linear-input DAG. Every
stored vertex is reachable, and its distinct numeric ID records its spine or
side-input occurrence. The source ResolutionDAG is the standard exact-ID
unfolding of that table. Its root is the actual final clause, which is empty
only in the refutation case; a zero-step derivation gives one input vertex. -/
@[attach_debt, blueprint "chap9__definition_9_3_2"]
theorem SLDDerivation.toResolutionDAG_exists (d : SLDDerivation) :
    ∃ g : LCS.Resolution.Method.FiniteGraph,
      g = d.resolutionGraph ∧
      ∃ hg : g.WellFormed,
        g.table.length = 2 * d.sequence.length - 1 ∧
        g.vertexIds.Perm (List.range (2 * d.sequence.length - 1)) ∧
        g.root = 2 * (d.sequence.length - 1) ∧
        g.node 0 = some ⟨d.sequence.head d.seqNonempty, none⟩ ∧
        (∀ j : Fin d.sequence.length,
          g.label (2 * j.val) = some (d.sequence.get j)) ∧
        (∀ i : Fin (d.sequence.length - 1),
          g.node (2 * i.val + 1) = some ⟨(d.steps i).sideClause, none⟩ ∧
          g.node (2 * i.val + 2) = some
            ⟨d.sequence.get ⟨i.val + 1, by omega⟩,
              some ⟨Literal.neg (d.steps i).selectedAtom, 2 * i.val, 2 * i.val + 1⟩⟩) ∧
        (d.sequence.length = 1 → g.table = [⟨d.sequence.head d.seqNonempty, none⟩]) ∧
        ∃ R : LCS.Resolution.Method.ResolutionDAG,
          R = g.toResolutionDAG hg ∧
          R.rootLabel = d.sequence.getLast d.seqNonempty ∧
          (isSLDRefutation d → R.rootLabel = Clause.empty) 

-- ========= Definition 9.3.2 (companion): sldResolutionMethod =========

/-- Definition 9.3.2 (companion): The SLD-resolution method succeeds when
    the same arbitrary program and finite goal family admit a validated refutation. -/
@[blueprint "chap9__definition_9_3_2"]
def sldResolutionMethod (D : Set Clause) (goals : List Clause) : Prop :=
  ∃ d : SLDDerivation,
    d.definiteClauses = D ∧ d.goals = goals ∧ isSLDRefutation d

/-- Soundness for the same original input: an arbitrary definite program and
finite negative goal family have no common valuation if their SLD method succeeds.
SQ17 includes an initially empty goal and its zero-step refutation. -/
@[attach_debt, blueprint "chap9__definition_9_3_2"]
theorem sldResolutionMethod_unsatisfiable (D : Set Clause) (goals : List Clause)
    (hRef : sldResolutionMethod D goals) :
    ¬ ∃ v : Nat → Bool,
      (∀ C ∈ D, Clause.satisfiedBy C v) ∧
      (∀ G ∈ goals, Clause.satisfiedBy G v)

/-- Any negative atom of a nonterminal residual goal can be selected in a
successful continuation over the same inputs and prefix (SQ20–SQ21).
The side clause is existentially supplied by that successful continuation. -/
@[attach_debt, blueprint "chap9__theorem_9_3_1"]
theorem sldRefutation_continueWithSelectedAtom
    (d : SLDDerivation) (hRef : isSLDRefutation d)
    (k : Fin (d.sequence.length - 1)) (P : Nat)
    (hP : Literal.neg P ∈ d.sequence.get ⟨k.val, by omega⟩) :
    ∃ d' : SLDDerivation,
      d'.definiteClauses = d.definiteClauses ∧ d'.goals = d.goals ∧
      isSLDRefutation d' ∧
      d'.sequence.take (k.val + 1) = d.sequence.take (k.val + 1) ∧
      ∃ hk : k.val < d'.sequence.length - 1,
        (d'.steps ⟨k.val, hk⟩).selectedAtom = P ∧
        (d'.steps ⟨k.val, hk⟩).sideClause ∈ d.definiteClauses ∧
        selectedAtomMatches (d'.sequence.get ⟨k.val, by omega⟩) P
          (d'.steps ⟨k.val, hk⟩).sideClause ∧
        d'.sequence.get ⟨k.val + 1, by omega⟩ =
          resolveStep (d'.sequence.get ⟨k.val, by omega⟩) P
            (d'.steps ⟨k.val, hk⟩).sideClause

-- ========= Definition 9.3.1 (companion): augmentClause =========

/-- Definition 9.3.1 (companion): Adds extra negative literals to a clause
    via set union: C ∪ (Clause.ofList extraLits). Used in the goal splitting
    rule to construct each clause of C'_i by adding neg P_{i+1},...,neg P_n. -/
@[blueprint "chap9__definition_9_3_1"]
def augmentClause (C : Clause) (extraLits : List Literal) : Clause :=
  Clause.union C (Clause.ofList extraLits)

-- ========= Definition 9.3.1 (companion): modifiedSubsequence =========

/-- Definition 9.3.1 (companion): Given a sequence C_i and extra literals,
    drop the last clause from C_i and append the extra literals to each
    remaining clause. Produces C'_i. -/
@[blueprint "chap9__definition_9_3_1"]
def modifiedSubsequence (seq : List Clause) (extraLits : List Literal)
    : List Clause :=
  match seq with
  | [] => []
  | [_] => []  -- drop the last clause
  | c :: rest => augmentClause c extraLits :: modifiedSubsequence rest extraLits

-- ========= Definition 9.3.1: linearize =========

/-- Definition 9.3.1: The noncomputable linearization specification closes every
    trivial label with its complementary pair before inspecting the rule below it.
    Nontrivial nodes follow the binary definite-step/goal-split equations. -/
@[blueprint "chap9__definition_9_3_1" (main := true)]
noncomputable def linearize : {S : ClauseSequent} → GCNFProofTree S → List Clause
  | _, .axiom_ _S _hOrd hTriv =>
    -- Rule (1): axiom neg P, P -> is converted to [{neg P}, Clause.empty]
    -- Extract the negative literal from the axiom. In a well-formed SLD axiom,
    -- S contains {[pos P], [neg P]} for some P. Use the triviality witness.
    let P := Classical.choose hTriv
    [Clause.single (Literal.neg P), Clause.empty]
  | _, .rule Gamma As B _Cs _ _ _hGammaOrd _hAsOrd leftTree rightTree _hNe _hSub _ _ =>
    letI : Decidable (ClauseSequent.isTrivial (Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)))) := Classical.propDecidable _
    if hAx : ClauseSequent.isTrivial (Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B))) then
      [Clause.single (Literal.neg (Classical.choose hAx)), Clause.empty]
    else
      match B with
      | Literal.pos P => Clause.single (Literal.neg P) :: linearize leftTree
      | Literal.neg _ =>
        modifiedSubsequence (linearize leftTree) [B] ++ linearize rightTree

-- ========= Example 9.3.1: Linearization example =========

/-- Example 9.3.1 (companion): The sequence corresponding to the left
    subtree: <{neg P_1}, {neg P_3, neg P_4}, {neg P_4}, square>. -/
@[blueprint "chap9__example_9_3_1"]
def exLeftSubtreeLinearization : List Clause :=
  [Clause.ofList [Literal.neg 1],
   Clause.ofList [Literal.neg 3, Literal.neg 4],
   Clause.ofList [Literal.neg 4],
   Clause.empty]

/-- Example 9.3.1 (companion): The sequence corresponding to the right
    subtree: <{neg P_2}, {neg P_3}, square>. -/
@[blueprint "chap9__example_9_3_1"]
def exRightSubtreeLinearization : List Clause :=
  [Clause.ofList [Literal.neg 2],
   Clause.ofList [Literal.neg 3],
   Clause.empty]

/-- Example 9.3.1: The linearization of the SLD-form proof from Example 9.2.1:
    <{neg P_1, neg P_2}, {neg P_3, neg P_4, neg P_2}, {neg P_4, neg P_2}, {neg P_2}, {neg P_3}, square>. -/
@[blueprint "chap9__example_9_3_1" (main := true)]
def exLinearizationResult : List Clause :=
  [Clause.ofList [Literal.neg 1, Literal.neg 2],
   Clause.ofList [Literal.neg 3, Literal.neg 4, Literal.neg 2],
   Clause.ofList [Literal.neg 4, Literal.neg 2],
   Clause.ofList [Literal.neg 2],
   Clause.ofList [Literal.neg 3],
   Clause.empty]

-- ========= Example 9.3.2: SLD-refutation example =========

/-- Example 9.3.2: The sequence from Example 9.3.1 is an SLD-refutation: an SLDDerivation
    with definiteClauses from Example 9.2.1, goals = [{neg 1, neg 2}], sequence = exLinearizationResult. -/
@[blueprint "chap9__example_9_3_2" (main := true)]
def exSLDRefutation : SLDDerivation where
  definiteClauses := fun C => C ∈
    [Clause.ofList [Literal.pos 3],
     Clause.ofList [Literal.pos 4],
     Clause.ofList [Literal.neg 3, Literal.neg 4, Literal.pos 1],
     Clause.ofList [Literal.neg 3, Literal.pos 2]]
  definiteValid := by
    intro C hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl | rfl | rfl
    all_goals
      refine ⟨⟨by unfold Clause.isOrdinary; native_decide, ?_⟩, ?_⟩
      · intro P Q hP hQ
        simp [Clause.ofList, Finset.mem_ofList] at hP hQ
        exact hP.trans hQ.symm
      · simp [Clause.ofList, Finset.mem_ofList]
  goals := [Clause.ofList [Literal.neg 1, Literal.neg 2]]
  sequence := exLinearizationResult
  goalsNegative := by
    intro C hC l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl
    all_goals simp [Clause.ofList, Finset.mem_ofList] at hl; rcases hl with rfl | rfl <;> trivial
  sequenceNegative := by
    intro C hC l hl
    simp only [exLinearizationResult, List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [Clause.ofList, Clause.empty, Finset.mem_ofList, Finset.mem_empty] at hl
    all_goals rcases hl with rfl | rfl | rfl <;> trivial
  seqNonempty := by simp [exLinearizationResult]
  initialIsGoal := by simp [exLinearizationResult]
  steps := fun i =>
    ([⟨1, Clause.ofList [Literal.neg 3, Literal.neg 4, Literal.pos 1]⟩,
      ⟨3, Clause.ofList [Literal.pos 3]⟩,
      ⟨4, Clause.ofList [Literal.pos 4]⟩,
      ⟨2, Clause.ofList [Literal.neg 3, Literal.pos 2]⟩,
      ⟨3, Clause.ofList [Literal.pos 3]⟩] : List SLDStepWitness).get
      ⟨i.val, by simpa [exLinearizationResult] using i.isLt⟩
  stepValid := fun ⟨i, hi⟩ => by
    unfold exLinearizationResult at hi ⊢
    have hi5 : i < 5 := by simp at hi; omega
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl
    · simp only [List.get]
      refine ⟨by change _ ∈ ([Clause.ofList [Literal.pos 3],
     Clause.ofList [Literal.pos 4],
     Clause.ofList [Literal.neg 3, Literal.neg 4, Literal.pos 1],
     Clause.ofList [Literal.neg 3, Literal.pos 2]] : List Clause); native_decide, ⟨by native_decide, by native_decide⟩, by native_decide⟩
    · simp only [List.get]
      refine ⟨by change _ ∈ ([Clause.ofList [Literal.pos 3],
     Clause.ofList [Literal.pos 4],
     Clause.ofList [Literal.neg 3, Literal.neg 4, Literal.pos 1],
     Clause.ofList [Literal.neg 3, Literal.pos 2]] : List Clause); native_decide, ⟨by native_decide, by native_decide⟩, by native_decide⟩
    · simp only [List.get]
      refine ⟨by change _ ∈ ([Clause.ofList [Literal.pos 3],
     Clause.ofList [Literal.pos 4],
     Clause.ofList [Literal.neg 3, Literal.neg 4, Literal.pos 1],
     Clause.ofList [Literal.neg 3, Literal.pos 2]] : List Clause); native_decide, ⟨by native_decide, by native_decide⟩, by native_decide⟩
    · simp only [List.get]
      refine ⟨by change _ ∈ ([Clause.ofList [Literal.pos 3],
     Clause.ofList [Literal.pos 4],
     Clause.ofList [Literal.neg 3, Literal.neg 4, Literal.pos 1],
     Clause.ofList [Literal.neg 3, Literal.pos 2]] : List Clause); native_decide, ⟨by native_decide, by native_decide⟩, by native_decide⟩
    · simp only [List.get]
      refine ⟨by change _ ∈ ([Clause.ofList [Literal.pos 3],
     Clause.ofList [Literal.pos 4],
     Clause.ofList [Literal.neg 3, Literal.neg 4, Literal.pos 1],
     Clause.ofList [Literal.neg 3, Literal.pos 2]] : List Clause); native_decide, ⟨by native_decide, by native_decide⟩, by native_decide⟩

-- ========= Example 9.3.3: Multiple goal SLD-refutations =========

/-- Example 9.3.3: A set S of Horn clauses with two goals S = {{P}, {Q}, {neg S, R},
    {neg R, neg P}, {neg R, neg Q}, {S}} where P=0, Q=1, R=2, S=3. -/
@[blueprint "chap9__example_9_3_3" (main := true)]
def exMultiGoalClauseSet : List Clause :=
  [Clause.ofList [Literal.pos 0],
   Clause.ofList [Literal.pos 1],
   Clause.ofList [Literal.neg 3, Literal.pos 2],
   Clause.ofList [Literal.neg 2, Literal.neg 0],
   Clause.ofList [Literal.neg 2, Literal.neg 1],
   Clause.ofList [Literal.pos 3]]

/-- Example 9.3.3: The SLD-refutation <{neg R, neg P}, {neg R}, {neg S}, square> resolving
    neg P against {P}, then neg R against {neg S, R}, then neg S against {S} to yield []. -/
@[blueprint "chap9__example_9_3_3" (main := true)]
def exMultiGoalRefutation1 : SLDDerivation where
  definiteClauses := fun C => C ∈
    [Clause.ofList [Literal.pos 0],
     Clause.ofList [Literal.pos 1],
     Clause.ofList [Literal.neg 3, Literal.pos 2],
     Clause.ofList [Literal.pos 3]]
  definiteValid := by
    intro C hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl | rfl | rfl
    all_goals
      refine ⟨⟨by unfold Clause.isOrdinary; native_decide, ?_⟩, ?_⟩
      · intro P Q hP hQ
        simp [Clause.ofList, Finset.mem_ofList] at hP hQ
        exact hP.trans hQ.symm
      · simp [Clause.ofList, Finset.mem_ofList]
  goals :=
    [Clause.ofList [Literal.neg 2, Literal.neg 0],
     Clause.ofList [Literal.neg 2, Literal.neg 1]]
  sequence :=
    [Clause.ofList [Literal.neg 2, Literal.neg 0],
     Clause.ofList [Literal.neg 2],
     Clause.ofList [Literal.neg 3],
     Clause.empty]
  goalsNegative := by
    intro C hC l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl
    all_goals simp [Clause.ofList, Finset.mem_ofList] at hl; rcases hl with rfl | rfl <;> trivial
  sequenceNegative := by
    intro C hC l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl | rfl | rfl
    all_goals simp [Clause.ofList, Clause.empty, Finset.mem_ofList, Finset.mem_empty] at hl
    all_goals rcases hl with rfl | rfl | rfl <;> trivial
  seqNonempty := by decide
  initialIsGoal := by simp
  steps := fun i =>
    ([⟨0, Clause.ofList [Literal.pos 0]⟩,
      ⟨2, Clause.ofList [Literal.neg 3, Literal.pos 2]⟩,
      ⟨3, Clause.ofList [Literal.pos 3]⟩] : List SLDStepWitness).get
      ⟨i.val, by simpa [] using i.isLt⟩
  stepValid := fun ⟨i, hi⟩ => by
    have hi3 : i < 3 := by simp at hi; omega
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl
    · simp only [List.get]
      refine ⟨by change _ ∈ ([Clause.ofList [Literal.pos 0],
     Clause.ofList [Literal.pos 1],
     Clause.ofList [Literal.neg 3, Literal.pos 2],
     Clause.ofList [Literal.pos 3]] : List Clause); native_decide, ⟨by native_decide, by native_decide⟩, by native_decide⟩
    · simp only [List.get]
      refine ⟨by change _ ∈ ([Clause.ofList [Literal.pos 0],
     Clause.ofList [Literal.pos 1],
     Clause.ofList [Literal.neg 3, Literal.pos 2],
     Clause.ofList [Literal.pos 3]] : List Clause); native_decide, ⟨by native_decide, by native_decide⟩, by native_decide⟩
    · simp only [List.get]
      refine ⟨by change _ ∈ ([Clause.ofList [Literal.pos 0],
     Clause.ofList [Literal.pos 1],
     Clause.ofList [Literal.neg 3, Literal.pos 2],
     Clause.ofList [Literal.pos 3]] : List Clause); native_decide, ⟨by native_decide, by native_decide⟩, by native_decide⟩

/-- Example 9.3.3: The SLD-refutation <{neg R, neg Q}, {neg R}, {neg S}, square> resolving
    neg Q against {Q}, then neg R against {neg S, R}, then neg S against {S} to yield []. -/
@[blueprint "chap9__example_9_3_3" (main := true)]
def exMultiGoalRefutation2 : SLDDerivation where
  definiteClauses := fun C => C ∈
    [Clause.ofList [Literal.pos 0],
     Clause.ofList [Literal.pos 1],
     Clause.ofList [Literal.neg 3, Literal.pos 2],
     Clause.ofList [Literal.pos 3]]
  definiteValid := by
    intro C hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl | rfl | rfl
    all_goals
      refine ⟨⟨by unfold Clause.isOrdinary; native_decide, ?_⟩, ?_⟩
      · intro P Q hP hQ
        simp [Clause.ofList, Finset.mem_ofList] at hP hQ
        exact hP.trans hQ.symm
      · simp [Clause.ofList, Finset.mem_ofList]
  goals :=
    [Clause.ofList [Literal.neg 2, Literal.neg 0],
     Clause.ofList [Literal.neg 2, Literal.neg 1]]
  sequence :=
    [Clause.ofList [Literal.neg 2, Literal.neg 1],
     Clause.ofList [Literal.neg 2],
     Clause.ofList [Literal.neg 3],
     Clause.empty]
  goalsNegative := by
    intro C hC l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl
    all_goals simp [Clause.ofList, Finset.mem_ofList] at hl; rcases hl with rfl | rfl <;> trivial
  sequenceNegative := by
    intro C hC l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl | rfl | rfl
    all_goals simp [Clause.ofList, Clause.empty, Finset.mem_ofList, Finset.mem_empty] at hl
    all_goals rcases hl with rfl | rfl | rfl <;> trivial
  seqNonempty := by decide
  initialIsGoal := by simp
  steps := fun i =>
    ([⟨1, Clause.ofList [Literal.pos 1]⟩,
      ⟨2, Clause.ofList [Literal.neg 3, Literal.pos 2]⟩,
      ⟨3, Clause.ofList [Literal.pos 3]⟩] : List SLDStepWitness).get
      ⟨i.val, by simpa [] using i.isLt⟩
  stepValid := fun ⟨i, hi⟩ => by
    have hi3 : i < 3 := by simp at hi; omega
    have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl
    · simp only [List.get]
      refine ⟨by change _ ∈ ([Clause.ofList [Literal.pos 0],
     Clause.ofList [Literal.pos 1],
     Clause.ofList [Literal.neg 3, Literal.pos 2],
     Clause.ofList [Literal.pos 3]] : List Clause); native_decide, ⟨by native_decide, by native_decide⟩, by native_decide⟩
    · simp only [List.get]
      refine ⟨by change _ ∈ ([Clause.ofList [Literal.pos 0],
     Clause.ofList [Literal.pos 1],
     Clause.ofList [Literal.neg 3, Literal.pos 2],
     Clause.ofList [Literal.pos 3]] : List Clause); native_decide, ⟨by native_decide, by native_decide⟩, by native_decide⟩
    · simp only [List.get]
      refine ⟨by change _ ∈ ([Clause.ofList [Literal.pos 0],
     Clause.ofList [Literal.pos 1],
     Clause.ofList [Literal.neg 3, Literal.pos 2],
     Clause.ofList [Literal.pos 3]] : List Clause); native_decide, ⟨by native_decide, by native_decide⟩, by native_decide⟩

-- ========= Example 9.3.3 (companion): clause set decomposition =========

/-- Example 9.3.3 (companion): Every definite clause used in the
    first SLD-refutation belongs to the clause set S. -/
@[blueprint "chap9__example_9_3_3"]
theorem exMultiGoalRefutation1_clauses_subset :
    ∀ C ∈ exMultiGoalRefutation1.definiteClauses, C ∈ exMultiGoalClauseSet 

/-- The two displayed refutations begin at distinct goals of the same finite
Horn input. Keeping either goal and the same definite part gives a GCNF′-provable
restriction, as does the full input (SQ20). -/
@[attach_debt, blueprint "chap9__example_9_3_3"]
theorem exMultiGoal_distinct_singleGoal_provable :
    let D := ClauseSequent.ofList
      [Clause.single (.pos 0), Clause.single (.pos 1),
       Clause.ofList [.neg 3, .pos 2], Clause.single (.pos 3)]
    let g := exMultiGoalRefutation1.sequence.head exMultiGoalRefutation1.seqNonempty
    let h := exMultiGoalRefutation2.sequence.head exMultiGoalRefutation2.seqNonempty
    g ≠ h ∧ isGoalClause g ∧ isGoalClause h ∧
    (∀ C ∈ D, isDefiniteClause C) ∧
    (∀ C, C ∈ D ↔ C ∈ exMultiGoalRefutation1.definiteClauses) ∧
    (∀ C, C ∈ D ↔ C ∈ exMultiGoalRefutation2.definiteClauses) ∧
    ClauseSequent.ofList exMultiGoalClauseSet =
      Finset.union D (ClauseSequent.ofList [g, h]) ∧
    GCNFProvable (ClauseSequent.ofList exMultiGoalClauseSet) ∧
    GCNFProvable (Finset.union D (ClauseSequent.single g)) ∧
    GCNFProvable (Finset.union D (ClauseSequent.single h))

/-- Linearize the actual subtree at a kernel path: false chooses the left
premise, true the right. An absent descendant has no output. -/
@[blueprint "chap9__example_9_3_1"]
noncomputable def linearizeAt : {S : ClauseSequent} → GCNFProofTree S →
    List Bool → Option (List Clause)
  | _, T, [] => some (linearize T)
  | _, .axiom_ _ _ _, _ :: _ => none
  | _, .rule _ _ _ _ _ _ _ _ left right _ _ _ _, b :: path =>
      if b then linearizeAt right path else linearizeAt left path

/-- The displayed left subtree of the exact Example 9.2.1 tree has the
four-entry output of Example 9.3.1; its root is unswapped (SQ18). -/
@[attach_debt, blueprint "chap9__example_9_3_1"]
theorem exLeftSubtree_linearize_eq :
    linearizeAt exSLDFormProof.kernel [false] = some exLeftSubtreeLinearization

/-- The displayed right subtree of the same tree has the three-entry output. -/
@[attach_debt, blueprint "chap9__example_9_3_1"]
theorem exRightSubtree_linearize_eq :
    linearizeAt exSLDFormProof.kernel [true] = some exRightSubtreeLinearization

/-- The exact worked tree produces the six-entry sequence. This finite
instance does not assert the unrestricted SQ18 linearization specification. -/
@[attach_debt, blueprint "chap9__example_9_3_1"]
theorem exSLDFormProof_linearize_eq :
    linearize exSLDFormProof.kernel = exLinearizationResult

-- ========= Example 9.3.1 (companion theorem): exLinearizationResult_eq =========

-- ATTACH-KEEP: native decision certificate must retain its front owner
/-- Finite check of the displayed concatenation of negative clauses. -/
theorem exLinearizationConcatenation_check :
    decide (exLinearizationResult =
      modifiedSubsequence exLeftSubtreeLinearization [Literal.neg 2] ++
        exRightSubtreeLinearization) = true := by
  native_decide

/-- The full-tree output is the concatenation of the two displayed subtree
outputs, and equals the same six-entry refutation sequence (SQ18). -/
@[blueprint "chap9__example_9_3_1"]
theorem exLinearizationResult_eq :
    linearize exSLDFormProof.kernel = exLinearizationResult ∧
    exLinearizationResult =
      modifiedSubsequence exLeftSubtreeLinearization [Literal.neg 2]
        ++ exRightSubtreeLinearization

-- ========= Example 9.3.2 (companion theorem): exSLDRefutation_isRefutation =========

/-- Example 9.3.2 (companion): Proof that the example SLD-derivation is
    indeed an SLD-refutation (last clause is empty). -/
@[blueprint "chap9__example_9_3_2"]
theorem exSLDRefutation_isRefutation : isSLDRefutation exSLDRefutation 

-- ========= Example 9.3.3 (companion theorems): refutation proofs =========

/-- Example 9.3.3 (companion): Proof that the first derivation is an
    SLD-refutation. -/
@[blueprint "chap9__example_9_3_3"]
theorem exMultiGoalRefutation1_isRefutation :
    isSLDRefutation exMultiGoalRefutation1 

/-- Example 9.3.3 (companion): Proof that the second derivation is an
    SLD-refutation. -/
@[blueprint "chap9__example_9_3_3"]
theorem exMultiGoalRefutation2_isRefutation :
    isSLDRefutation exMultiGoalRefutation2 

-- ========= Auxiliary lemmas for linearization correctness =========

-- retained: used by LCS.SLD.Propositional.Part2
/-- The linearization of any proof tree has length at least 2. -/
theorem linearize_length_ge_two : {S : ClauseSequent} → (T : GCNFProofTree S) →
    (linearize T).length ≥ 2
  | _, .axiom_ _ _hOrd _ => by simp [linearize]
  | _, .rule Gamma As B _ _ _ _hGammaOrd _hAsOrd leftTree rightTree _ _ _ _ => by
    classical
    by_cases hAx : ClauseSequent.isTrivial (Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)))
    · simp [linearize, hAx]
    have ihLeft := linearize_length_ge_two leftTree
    have ihRight := linearize_length_ge_two rightTree
    cases B with
    | pos _ =>
      simp only [linearize, dif_neg hAx, List.length_cons]
      have := ihLeft; omega
    | neg _ =>
      simp only [linearize, dif_neg hAx, List.length_append]
      have := ihRight; omega

-- retained: used by LCS.SLD.Propositional.Part2
/-- If a list has length >= 2, its modifiedSubsequence is nonempty. -/
theorem modifiedSubsequence_nonempty_of_ge_two
    (seq : List Clause) (extra : List Literal)
    (h : seq.length ≥ 2) :
    modifiedSubsequence seq extra ≠ [] := by
-- BEGIN PROOF
  match seq, h with
  | _ :: _ :: _, _ => simp [modifiedSubsequence]



-- retained: used by LCS.SLD.Propositional.Part2
/-- A singleton negative clause {neg P} is a goal clause (early version
    for use by helper lemmas). -/
theorem isGoalClause_single_neg' (P : Nat) :
    isGoalClause (Clause.single (Literal.neg P)) :=
  LCS.SLD.SLDForm.Completeness.singleton_neg_is_goal P







-- retained: used by LCS.SLD.Propositional.Part2
/-- The linearization of any proof tree is nonempty. -/
theorem linearize_nonempty : {S : ClauseSequent} → (T : GCNFProofTree S) → linearize T ≠ []
  | _, .axiom_ _S _hOrd _hTriv => by simp [linearize]
  | _, .rule Gamma As B _Cs _ _ _hGammaOrd _hAsOrd leftTree rightTree _hNe _hSub _ _ => by
    classical
    by_cases hAx : ClauseSequent.isTrivial (Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)))
    · simp [linearize, hAx]
    have ihLeft := linearize_nonempty leftTree
    have ihRight := linearize_nonempty rightTree
    cases B with
    | pos _P =>
      simp [linearize, dif_neg hAx]
    | neg _ =>
      simp only [linearize, dif_neg hAx]
      exact List.append_ne_nil_of_right_ne_nil _ (ihRight)





-- retained: used by LCS.SLD.Propositional.Part2
/-- A singleton negative clause {neg P} is a goal clause. -/
theorem isGoalClause_single_neg (P : Nat) : isGoalClause (Clause.single (Literal.neg P)) :=
  LCS.SLD.SLDForm.Completeness.singleton_neg_is_goal P









end LCS.SLD.Propositional
end

attribute [blueprint "chap9__definition_9_3_2"] LCS.SLD.Propositional.SLDDerivation.seqNonempty
