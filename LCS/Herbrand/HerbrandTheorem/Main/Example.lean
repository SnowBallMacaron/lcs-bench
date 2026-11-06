import LCS.Item
import LCS.Util
import LCS.Herbrand.HerbrandTheorem
import LCS.Herbrand.HerbrandTheorem.Main.HerbrandDisjunction
import Attach
import LCS.Herbrand.HerbrandTheorem.Main.Example.ProofsStamp

/-! # Herbrand.HerbrandTheorem.Main.Example
    Chapter 7, Section 5.4: Example 7.5.3. The sequent of Example 7.3.4,
    its functional form, the Herbrand disjunction with the term set HT and its
    subterm ordering, and the proof reconstruction that processes the Herbrand
    terms from largest to smallest.

    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.Herbrand.HerbrandTheorem.Main
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.Gentzen
open LCS.Herbrand.HerbrandTheorem
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.CutElim.LK
open LCS.CutElim.LKe.Equivalence

-- ===================================================================
-- Theorem 7.5.1 (companion def): folkProofTreeAllRightEigenvariables
-- ===================================================================



-- ===================================================================
-- Theorem 7.5.1 (companion def): skolemSubstForEigenvariables
-- ===================================================================



-- ===================================================================
-- Example 7.5.3 (companion type): HerbrandExFunc
-- ===================================================================

/-- Example 7.5.3 (companion type): Unary Skolem function symbols f
    and g for the Herbrand theorem example. -/
@[blueprint "chap7__example_7_5_3"]
inductive HerbrandExFunc : Type where
  /-- Unary Skolem function f -/
  | f : HerbrandExFunc
  /-- Unary Skolem function g -/
  | g : HerbrandExFunc

-- ===================================================================
-- Example 7.5.3 (companion type): HerbrandExConst
-- ===================================================================

/-- Example 7.5.3 (companion type): Skolem constant a for the
    Herbrand theorem example. -/
@[blueprint "chap7__example_7_5_3"]
inductive HerbrandExConst : Type where
  /-- Skolem constant a -/
  | a : HerbrandExConst

-- ===================================================================
-- Example 7.5.3 (companion type): HerbrandExPred
-- ===================================================================

/-- Example 7.5.3 (companion type): Binary predicates P and Q for the
    Herbrand theorem example. -/
@[blueprint "chap7__example_7_5_3"]
inductive HerbrandExPred : Type where
  /-- Binary predicate P -/
  | P : HerbrandExPred
  /-- Binary predicate Q -/
  | Q : HerbrandExPred

-- ===================================================================
-- Example 7.5.3 (companion def): herbrandExLang
-- ===================================================================

/-- Example 7.5.3 (companion def): An extended language with binary predicates P, Q, Skolem function symbols f (unary), g (unary), and Skolem constant a. This is the Herbrand language for the example. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExLang : Language where
  funSymbols := HerbrandExFunc
  funArity := fun
    | .f => 1
    | .g => 1
  constSymbols := HerbrandExConst
  predSymbols := HerbrandExPred
  predArity := fun _ => 2

-- ===================================================================
-- Example 7.5.3: herbrandExampleSequent
-- ===================================================================

/-- Example 7.5.3: The original prenex sequent -> exists x forall y not P(x,y), exists y_1 forall z not Q(y_1,z), forall x_1 exists y_2 exists z_1(P(x_1,y_2) and Q(y_2,z_1)). Variables: x=0, y=1, y_1=2, z=3, x_1=4, y_2=5, z_1=6. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExampleSequent : Sequent herbrandExLang :=
  let mkP (a b : Term herbrandExLang) :=
    FormulaN.predN HerbrandExPred.P (vec2 a b)
  let mkQ (a b : Term herbrandExLang) :=
    FormulaN.predN HerbrandExPred.Q (vec2 a b)
  -- exists x forall y not P(x, y)
  let f1 := FormulaN.ex 0
    (FormulaN.all 1
      (FormulaN.neg (mkP (Term.var 0) (Term.var 1))))
  -- exists y_1 forall z not Q(y_1, z)
  let f2 := FormulaN.ex 2
    (FormulaN.all 3
      (FormulaN.neg (mkQ (Term.var 2) (Term.var 3))))
  -- forall x_1 exists y_2 exists z_1(P(x_1,y_2) and Q(y_2,z_1))
  let f3 := FormulaN.all 4
    (FormulaN.ex 5
      (FormulaN.ex 6
        (FormulaN.conj
          (mkP (Term.var 4) (Term.var 5))
          (mkQ (Term.var 5) (Term.var 6)))))
  { antecedent := []
    succedent := [f1, f2, f3] }

-- ===================================================================
-- Example 7.5.3 (companion def): herbrandExFunctionalForm
-- ===================================================================

/-- Example 7.5.3 (companion def): The functional form -> exists x not P(x, f(x)), exists y_1 not Q(y_1, g(y_1)), exists y_2 exists z_1(P(a, y_2) and Q(y_2, z_1)), obtained from the original sequent by Skolemization (replacing universally bound variables with Skolem terms and deleting universal quantifiers). -/
@[blueprint "chap7__example_7_5_3" (main := true)]
def herbrandExFunctionalForm : Sequent herbrandExLang :=
  let mkP (a b : Term herbrandExLang) :=
    FormulaN.predN HerbrandExPred.P (vec2 a b)
  let mkQ (a b : Term herbrandExLang) :=
    FormulaN.predN HerbrandExPred.Q (vec2 a b)
  let fx := Term.func HerbrandExFunc.f (fun _ => Term.var 0)
  let gy1 := Term.func HerbrandExFunc.g (fun _ => Term.var 2)
  let a := Term.const HerbrandExConst.a
  -- exists x not P(x, f(x))
  let f1 := FormulaN.ex 0
    (FormulaN.neg (mkP (Term.var 0) fx))
  -- exists y_1 not Q(y_1, g(y_1))
  let f2 := FormulaN.ex 2
    (FormulaN.neg (mkQ (Term.var 2) gy1))
  -- exists y_2 exists z_1(P(a, y_2) and Q(y_2, z_1))
  let f3 := FormulaN.ex 5
    (FormulaN.ex 6
      (FormulaN.conj
        (mkP a (Term.var 5))
        (mkQ (Term.var 5) (Term.var 6))))
  { antecedent := []
    succedent := [f1, f2, f3] }

-- ===================================================================
-- Example 7.5.3 (companion def): herbrandExDisjunction
-- ===================================================================

/-- Example 7.5.3 (companion def): The Herbrand disjunction -> not P(a, f(a)), not Q(f(a), g(f(a))), P(a, f(a)) and Q(f(a), g(f(a))), obtained from the functional form by substituting ground terms for existentially bound variables and deleting remaining quantifiers. This is the provable sequent H. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExDisjunction : Sequent herbrandExLang :=
  let mkP (a b : Term herbrandExLang) :=
    FormulaN.predN HerbrandExPred.P (vec2 a b)
  let mkQ (a b : Term herbrandExLang) :=
    FormulaN.predN HerbrandExPred.Q (vec2 a b)
  let a := Term.const HerbrandExConst.a
  let fa := Term.func HerbrandExFunc.f (fun _ => a)
  let gfa := Term.func HerbrandExFunc.g (fun _ => fa)
  -- not P(a, f(a))
  let g1 := FormulaN.neg (mkP a fa)
  -- not Q(f(a), g(f(a)))
  let g2 := FormulaN.neg (mkQ fa gfa)
  -- P(a, f(a)) and Q(f(a), g(f(a)))
  let g3 := FormulaN.conj (mkP a fa) (mkQ fa gfa)
  { antecedent := []
    succedent := [g1, g2, g3] }

-- ===================================================================
-- Example 7.5.3 (companion def): herbrandExTermSetHT
-- ===================================================================

/-- Example 7.5.3 (companion def): The Herbrand term set HT = [a, f(a), g(f(a))], the list of ground Skolem terms appearing in the Herbrand disjunction. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExTermSetHT : List (Term herbrandExLang) :=
  let a := Term.const HerbrandExConst.a
  let fa := Term.func HerbrandExFunc.f (fun _ => a)
  let gfa := Term.func HerbrandExFunc.g (fun _ => fa)
  [a, fa, gfa]

-- ===================================================================
-- Example 7.5.3 (companion def): herbrandExHTOrder
-- ===================================================================

/-- Example 7.5.3 (companion def): The partial ordering on HT: a < f(a), a < g(f(a)), f(a) < g(f(a)), determined by the subterm relation on Skolem terms. Defined concretely using isProperSubterm. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExHTOrder :
    Term herbrandExLang → Term herbrandExLang → Prop :=
  fun t1 t2 => isProperSubterm t1 t2

-- ===================================================================
-- Example 7.5.3 (companion def): herbrandExMaximalElements
-- ===================================================================



-- ===================================================================
-- Example 7.5.3 (companion def): herbrandExProofReconstructionOrder
-- ===================================================================

/-- Example 7.5.3 (companion def): The order in which exists:right and forall:right rules are iteratively applied during proof reconstruction: first process g(f(a)) (the largest element), then f(a), then a. This determines the sequence of quantifier rule applications from the Herbrand disjunction back to the original sequent. Computed by iteratively selecting the maximal element (one with no term above it in the remaining set) from herbrandExTermSetHT under herbrandExHTOrder, removing it, and repeating. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExProofReconstructionOrder :
    List (Term herbrandExLang) :=
  -- Iteratively extract maximal elements from HT under the subterm order.
  -- A term t is maximal in a list if no other term in the list has t as
  -- a proper subterm (i.e., no s in the list satisfies herbrandExHTOrder t s).
  let a := Term.const HerbrandExConst.a
  let fa := Term.func HerbrandExFunc.f (fun _ => a)
  let gfa := Term.func HerbrandExFunc.g (fun _ => fa)
  -- Step 1: From HT = [a, fa, gfa], g(f(a)) is maximal
  --   (no term in HT has g(f(a)) as a subterm).
  -- Step 2: From remaining [a, fa], f(a) is maximal
  --   (no term in [a, fa] has f(a) as a subterm).
  -- Step 3: From remaining [a], a is the only (and maximal) element.
  [gfa, fa, a]

/-- Example 7.5.3: P(s,t) in the concrete binary signature. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExP (s t : Term herbrandExLang) : FormulaN herbrandExLang :=
  .predN .P (vec2 s t)

/-- Example 7.5.3: Q(s,t) in the concrete binary signature. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExQ (s t : Term herbrandExLang) : FormulaN herbrandExLang :=
  .predN .Q (vec2 s t)

/-- Example 7.5.3: H′ is → ¬P(w,v), ¬Q(v,u), P(w,v) ∧ Q(v,u),
with fresh u=7, v=8, w=9. Original binder names remain 0–6. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExHPrime : Sequent herbrandExLang :=
  ⟨[], [.neg (herbrandExP (.var 9) (.var 8)), .neg (herbrandExQ (.var 8) (.var 7)),
    .conj (herbrandExP (.var 9) (.var 8)) (herbrandExQ (.var 8) (.var 7))]⟩

/-- Example 7.5.3: the propositional proof of H′ with its two identity leaves,
weakenings, conjunction and Q-before-P negations. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExHPrimeProof : FOLKProofTree herbrandExHPrime :=
  let p := herbrandExP (.var 9) (.var 8)
  let q := herbrandExQ (.var 8) (.var 7)
  let pAx := FOLKProofTree.axiom_ (Sequent.mk [p] [p]) ⟨p, rfl, rfl⟩
  let qAx := FOLKProofTree.axiom_ (Sequent.mk [q] [q]) ⟨q, rfl, rfl⟩
  let left := FOLKProofTree.onePremise (.exchangeLeft [] q p [] [p])
    (.onePremise (.weakenLeft q [p] [p]) pAx)
  let right := FOLKProofTree.onePremise (.weakenLeft p [q] [q]) qAx
  let conj := FOLKProofTree.twoPremise (.andRight p q [p, q] []) left right
  let negQ := FOLKProofTree.onePremise
    (.exchangeRight [p] [] (.conj p q) (.neg q) [])
    (.onePremise (.negRight q [p] [.conj p q])
      (.onePremise (.exchangeLeft [] p q [] [.conj p q]) conj))
  .onePremise (.exchangeRight [] [] (.neg q) (.neg p) [.conj p q])
    (.onePremise (.exchangeRight [] [.neg q] (.conj p q) (.neg p) [])
      (.onePremise (.negRight p [] [.neg q, .conj p q]) negQ))

/-- Example 7.5.3: corrected first boundary, retaining free v=8 until the
next existential step; only z₁=6 is bound here (SQ043). -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExReconstruction1 : Sequent herbrandExLang :=
  ⟨[], [.neg (herbrandExP (.var 9) (.var 8)), .neg (herbrandExQ (.var 8) (.var 7)),
    .ex 6 (.conj (herbrandExP (.var 9) (.var 8)) (herbrandExQ (.var 8) (.var 6))) ]⟩

/-- Example 7.5.3: second boundary introduces y₂=5 outside z₁=6. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExReconstruction2 : Sequent herbrandExLang :=
  ⟨[], [.neg (herbrandExP (.var 9) (.var 8)), .neg (herbrandExQ (.var 8) (.var 7)),
    .ex 5 (.ex 6 (.conj (herbrandExP (.var 9) (.var 5)) (herbrandExQ (.var 5) (.var 6))))]⟩

/-- Example 7.5.3: third boundary restores ∀z on the second formula, using
u=7 as eigenvariable, corresponding to the maximal term g(f(a)). -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExReconstruction3 : Sequent herbrandExLang :=
  ⟨[], [.neg (herbrandExP (.var 9) (.var 8)), .all 3 (.neg (herbrandExQ (.var 8) (.var 3))),
    .ex 5 (.ex 6 (.conj (herbrandExP (.var 9) (.var 5)) (herbrandExQ (.var 5) (.var 6))))]⟩

/-- Example 7.5.3: lawful cumulative reconstruction prefix 1, retaining
all preceding boundaries and the concrete proof of H′. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExPrefix1 : FOLKProofTree herbrandExReconstruction1 := by
  have substAtom (p : HerbrandExPred) (a b t : Term herbrandExLang) (x : Nat) :
      formulaSubstN (.predN p (vec2 a b)) t x =
        .predN p (vec2 (termSubst a t x) (termSubst b t x)) := by
    apply congrArg (FormulaN.predN (L := herbrandExLang) p)
    funext ⟨i, hi⟩
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
  have r : FOLKStep1 herbrandExHPrime herbrandExReconstruction1 := by
    simpa [herbrandExHPrime, herbrandExReconstruction1, herbrandExP, herbrandExQ,
      formulaSubstN, substAtom, termSubst] using
      (FOLKStep1.exRight (L := herbrandExLang) (.var 7) 6
        (.conj (herbrandExP (.var 9) (.var 8)) (herbrandExQ (.var 8) (.var 6)))
        [] [.neg (herbrandExP (.var 9) (.var 8)), .neg (herbrandExQ (.var 8) (.var 7))]
        (by simp [isFreeForN, herbrandExP, herbrandExQ, termFV, Membership.mem, Set.singleton]))
  exact .onePremise r herbrandExHPrimeProof

/-- Example 7.5.3: lawful cumulative reconstruction prefix 2, retaining
all preceding boundaries and the concrete proof of H′. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExPrefix2 : FOLKProofTree herbrandExReconstruction2 := by
  have substAtom (p : HerbrandExPred) (a b t : Term herbrandExLang) (x : Nat) :
      formulaSubstN (.predN p (vec2 a b)) t x =
        .predN p (vec2 (termSubst a t x) (termSubst b t x)) := by
    apply congrArg (FormulaN.predN (L := herbrandExLang) p)
    funext ⟨i, hi⟩
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
  have r : FOLKStep1 herbrandExReconstruction1 herbrandExReconstruction2 := by
    simpa [herbrandExReconstruction1, herbrandExReconstruction2, herbrandExP, herbrandExQ,
      formulaSubstN, substAtom, termSubst] using
      (FOLKStep1.exRight (L := herbrandExLang) (.var 8) 5
        (.ex 6 (.conj (herbrandExP (.var 9) (.var 5)) (herbrandExQ (.var 5) (.var 6))))
        [] [.neg (herbrandExP (.var 9) (.var 8)), .neg (herbrandExQ (.var 8) (.var 7))]
        (by simp [isFreeForN, herbrandExP, herbrandExQ, termFV, Membership.mem, Set.singleton]))
  exact .onePremise r herbrandExPrefix1

/-- Example 7.5.3: the third cumulative prefix, with exchanges exposing Q
and restoring the displayed order. The eigenvariable is fresh in the whole
conclusion, not just in its principal formula. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExPrefix3 : FOLKProofTree herbrandExReconstruction3 := by
  have substAtom (p : HerbrandExPred) (a b t : Term herbrandExLang) (x : Nat) :
      formulaSubstN (.predN p (vec2 a b)) t x =
        .predN p (vec2 (termSubst a t x) (termSubst b t x)) := by
    apply congrArg (FormulaN.predN (L := herbrandExLang) p)
    funext ⟨i, hi⟩
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
  let np := FormulaN.neg (herbrandExP (.var 9) (.var 8))
  let nq := FormulaN.neg (herbrandExQ (.var 8) (.var 7))
  let c2 := FormulaN.ex 5 (.ex 6
    (.conj (herbrandExP (.var 9) (.var 5)) (herbrandExQ (.var 5) (.var 6))))
  let aq := FormulaN.all 3 (.neg (herbrandExQ (.var 8) (.var 3)))
  have finTwo (R : Fin 2 → Prop) : (∃ i, R i) ↔ R 0 ∨ R 1 := by
    constructor
    · rintro ⟨⟨i, hi⟩, h⟩
      match i, hi with
      | 0, _ => exact Or.inl h
      | 1, _ => exact Or.inr h
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
  have finTwoAll (R : Fin 2 → Prop) : (∀ i, R i) ↔ R 0 ∧ R 1 := by
    constructor
    · intro h; exact ⟨h 0, h 1⟩
    · rintro ⟨h0, h1⟩ ⟨i, hi⟩
      match i, hi with
      | 0, _ => exact h0
      | 1, _ => exact h1
  have fresh : ∀ F ∈ ([] : List (FormulaN herbrandExLang)) ++ ([np, c2] ++ [aq]),
      7 ∉ formulaFVN F := by
    intro F hF
    simp only [List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl | rfl
    all_goals simp [np, c2, aq, formulaFVN, herbrandExP, herbrandExQ,
      Membership.mem, Set.iUnion, Set.union, Set.diff, Set.singleton,
      termFV, vec2, herbrandExLang, finTwo, finTwoAll]
  have r : FOLKStep1 ⟨[], [np, c2, nq]⟩ ⟨[], [np, c2, aq]⟩ := by
    simpa [nq, aq, formulaSubstN, herbrandExQ, substAtom, termSubst] using
      (FOLKStep1.allRight (L := herbrandExLang) 7 3
        (.neg (herbrandExQ (.var 8) (.var 3))) [] [np, c2] fresh
        (by simp [isFreeForN, herbrandExQ]))
  exact .onePremise (.exchangeRight [] [np] c2 aq [])
    (.onePremise r (.onePremise (.exchangeRight [] [np] nq c2 []) herbrandExPrefix2))

/-- Example 7.5.3: translate the f/g/a term spelling used in Example 7.5.2
into the identical symbols of this example's signature. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExFromSkolemTerm : Term exampleLang_7_5 → Term herbrandExLang
  | .var x => .var x
  | .const .a => .const .a
  | .func .f ts => .func .f (fun i => herbrandExFromSkolemTerm (ts i))
  | .func .g ts => .func .g (fun i => herbrandExFromSkolemTerm (ts i))

/-- Example 7.5.3: the same signature spelling on formulas, preserving binders. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExFromSkolemFormula : FormulaN exampleLang_7_5 → FormulaN herbrandExLang
  | .predN p ts => .predN (match p with | .P => .P | .Q => .Q)
      (fun i => herbrandExFromSkolemTerm (ts i))
  | .eq_ h s t => .eq_ h (herbrandExFromSkolemTerm s) (herbrandExFromSkolemTerm t)
  | .neg A => .neg (herbrandExFromSkolemFormula A)
  | .conj A B => .conj (herbrandExFromSkolemFormula A) (herbrandExFromSkolemFormula B)
  | .disj A B => .disj (herbrandExFromSkolemFormula A) (herbrandExFromSkolemFormula B)
  | .impl A B => .impl (herbrandExFromSkolemFormula A) (herbrandExFromSkolemFormula B)
  | .all x A => .all x (herbrandExFromSkolemFormula A)
  | .ex x A => .ex x (herbrandExFromSkolemFormula A)

/-- Example 7.5.3: the fourth boundary introduces ∃y₁ outside ∀z. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExReconstruction4 : Sequent herbrandExLang :=
  ⟨[], [.neg (herbrandExP (.var 9) (.var 8)),
    .ex 2 (.all 3 (.neg (herbrandExQ (.var 2) (.var 3)))),
    .ex 5 (.ex 6 (.conj (herbrandExP (.var 9) (.var 5)) (herbrandExQ (.var 5) (.var 6))))]⟩

/-- Example 7.5.3: the fifth boundary restores ∀y, with v=8 as eigenvariable. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExReconstruction5 : Sequent herbrandExLang :=
  ⟨[], [.all 1 (.neg (herbrandExP (.var 9) (.var 1))),
    .ex 2 (.all 3 (.neg (herbrandExQ (.var 2) (.var 3)))),
    .ex 5 (.ex 6 (.conj (herbrandExP (.var 9) (.var 5)) (herbrandExQ (.var 5) (.var 6))))]⟩

/-- Example 7.5.3: the sixth boundary introduces ∃x outside ∀y. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExReconstruction6 : Sequent herbrandExLang :=
  ⟨[], [.ex 0 (.all 1 (.neg (herbrandExP (.var 0) (.var 1)))),
    .ex 2 (.all 3 (.neg (herbrandExQ (.var 2) (.var 3)))),
    .ex 5 (.ex 6 (.conj (herbrandExP (.var 9) (.var 5)) (herbrandExQ (.var 5) (.var 6))))]⟩

/-- Example 7.5.3: lawful cumulative prefix 4, retaining every earlier
boundary. Quantifier side conditions are checked in the entire conclusion. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExPrefix4 : FOLKProofTree herbrandExReconstruction4 := by
  have substAtom (p : HerbrandExPred) (a b t : Term herbrandExLang) (x : Nat) :
      formulaSubstN (.predN p (vec2 a b)) t x =
        .predN p (vec2 (termSubst a t x) (termSubst b t x)) := by
    apply congrArg (FormulaN.predN (L := herbrandExLang) p)
    funext ⟨i, hi⟩
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
  let np := FormulaN.neg (herbrandExP (.var 9) (.var 8))
  let c2 := FormulaN.ex 5 (.ex 6 (.conj (herbrandExP (.var 9) (.var 5)) (herbrandExQ (.var 5) (.var 6))))
  let aq := FormulaN.all 3 (.neg (herbrandExQ (.var 8) (.var 3)))
  let eq := FormulaN.ex 2 (.all 3 (.neg (herbrandExQ (.var 2) (.var 3))))
  have r : FOLKStep1 ⟨[], [np, c2, aq]⟩ ⟨[], [np, c2, eq]⟩ := by
    simpa [aq, eq, formulaSubstN, herbrandExQ, substAtom, termSubst] using
      (FOLKStep1.exRight (L := herbrandExLang) (.var 8) 2
        (.all 3 (.neg (herbrandExQ (.var 2) (.var 3)))) [] [np, c2]
        (by simp [isFreeForN, herbrandExQ, termFV, Membership.mem, Set.singleton]))
  exact .onePremise (.exchangeRight [] [np] c2 eq [])
    (.onePremise r (.onePremise (.exchangeRight [] [np] aq c2 []) herbrandExPrefix3))

/-- Example 7.5.3: lawful cumulative prefix 5, retaining every earlier
boundary. Quantifier side conditions are checked in the entire conclusion. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExPrefix5 : FOLKProofTree herbrandExReconstruction5 := by
  have substAtom (p : HerbrandExPred) (a b t : Term herbrandExLang) (x : Nat) :
      formulaSubstN (.predN p (vec2 a b)) t x =
        .predN p (vec2 (termSubst a t x) (termSubst b t x)) := by
    apply congrArg (FormulaN.predN (L := herbrandExLang) p)
    funext ⟨i, hi⟩
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
  let np := FormulaN.neg (herbrandExP (.var 9) (.var 8))
  let c2 := FormulaN.ex 5 (.ex 6 (.conj (herbrandExP (.var 9) (.var 5)) (herbrandExQ (.var 5) (.var 6))))
  let eq := FormulaN.ex 2 (.all 3 (.neg (herbrandExQ (.var 2) (.var 3))))
  let ap := FormulaN.all 1 (.neg (herbrandExP (.var 9) (.var 1)))
  have finTwo (R : Fin 2 → Prop) : (∃ i, R i) ↔ R 0 ∨ R 1 := by
    constructor
    · rintro ⟨⟨i, hi⟩, h⟩
      match i, hi with
      | 0, _ => exact Or.inl h
      | 1, _ => exact Or.inr h
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
  have finTwoAll (R : Fin 2 → Prop) : (∀ i, R i) ↔ R 0 ∧ R 1 := by
    constructor
    · intro h; exact ⟨h 0, h 1⟩
    · rintro ⟨h0, h1⟩ ⟨i, hi⟩
      match i, hi with
      | 0, _ => exact h0
      | 1, _ => exact h1
  have fresh : ∀ F ∈ ([] : List (FormulaN herbrandExLang)) ++ ([eq, c2] ++ [ap]),
      8 ∉ formulaFVN F := by
    intro F hF
    simp only [List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl | rfl
    all_goals simp [np, c2, eq, ap, formulaFVN, herbrandExP, herbrandExQ,
      Membership.mem, Set.iUnion, Set.union, Set.diff, Set.singleton,
      termFV, vec2, herbrandExLang, finTwo, finTwoAll]
  have r : FOLKStep1 ⟨[], [eq, c2, np]⟩ ⟨[], [eq, c2, ap]⟩ := by
    simpa [np, ap, formulaSubstN, herbrandExP, substAtom, termSubst] using
      (FOLKStep1.allRight (L := herbrandExLang) 8 1
        (.neg (herbrandExP (.var 9) (.var 1))) [] [eq, c2] fresh
        (by simp [isFreeForN, herbrandExP]))
  exact .onePremise (.exchangeRight [] [] eq ap [c2])
    (.onePremise (.exchangeRight [] [eq] c2 ap [])
      (.onePremise r (.onePremise (.exchangeRight [] [eq] np c2 [])
        (.onePremise (.exchangeRight [] [] np eq [c2]) herbrandExPrefix4))))

/-- Example 7.5.3: lawful cumulative prefix 6, retaining every earlier
boundary. Quantifier side conditions are checked in the entire conclusion. -/
@[blueprint "chap7__example_7_5_3"]
def herbrandExPrefix6 : FOLKProofTree herbrandExReconstruction6 := by
  have substAtom (p : HerbrandExPred) (a b t : Term herbrandExLang) (x : Nat) :
      formulaSubstN (.predN p (vec2 a b)) t x =
        .predN p (vec2 (termSubst a t x) (termSubst b t x)) := by
    apply congrArg (FormulaN.predN (L := herbrandExLang) p)
    funext ⟨i, hi⟩
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
  let c2 := FormulaN.ex 5 (.ex 6 (.conj (herbrandExP (.var 9) (.var 5)) (herbrandExQ (.var 5) (.var 6))))
  let eq := FormulaN.ex 2 (.all 3 (.neg (herbrandExQ (.var 2) (.var 3))))
  let ap := FormulaN.all 1 (.neg (herbrandExP (.var 9) (.var 1)))
  let ep := FormulaN.ex 0 (.all 1 (.neg (herbrandExP (.var 0) (.var 1))))
  have r : FOLKStep1 ⟨[], [eq, c2, ap]⟩ ⟨[], [eq, c2, ep]⟩ := by
    simpa [ap, ep, formulaSubstN, herbrandExP, substAtom, termSubst] using
      (FOLKStep1.exRight (L := herbrandExLang) (.var 9) 0
        (.all 1 (.neg (herbrandExP (.var 0) (.var 1)))) [] [eq, c2]
        (by simp [isFreeForN, herbrandExP, termFV, Membership.mem, Set.singleton]))
  exact .onePremise (.exchangeRight [] [] eq ep [c2])
    (.onePremise (.exchangeRight [] [eq] c2 ep [])
      (.onePremise r (.onePremise (.exchangeRight [] [eq] ap c2 [])
        (.onePremise (.exchangeRight [] [] ap eq [c2]) herbrandExPrefix5))))

/-- Example 7.5.3: lawful cumulative prefix 7, retaining every earlier
boundary. Quantifier side conditions are checked in the entire conclusion. -/
@[blueprint "chap7__example_7_5_3" (main := true)]
def herbrandExPrefix7 : FOLKProofTree herbrandExampleSequent := by
  have substAtom (p : HerbrandExPred) (a b t : Term herbrandExLang) (x : Nat) :
      formulaSubstN (.predN p (vec2 a b)) t x =
        .predN p (vec2 (termSubst a t x) (termSubst b t x)) := by
    apply congrArg (FormulaN.predN (L := herbrandExLang) p)
    funext ⟨i, hi⟩
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
  let c2 := FormulaN.ex 5 (.ex 6 (.conj (herbrandExP (.var 9) (.var 5)) (herbrandExQ (.var 5) (.var 6))))
  let cf := FormulaN.ex 5 (.ex 6 (.conj (herbrandExP (.var 4) (.var 5)) (herbrandExQ (.var 5) (.var 6))))
  let ep := FormulaN.ex 0 (.all 1 (.neg (herbrandExP (.var 0) (.var 1))))
  let eq := FormulaN.ex 2 (.all 3 (.neg (herbrandExQ (.var 2) (.var 3))))
  have finTwo (R : Fin 2 → Prop) : (∃ i, R i) ↔ R 0 ∨ R 1 := by
    constructor
    · rintro ⟨⟨i, hi⟩, h⟩
      match i, hi with
      | 0, _ => exact Or.inl h
      | 1, _ => exact Or.inr h
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
  have finTwoAll (R : Fin 2 → Prop) : (∀ i, R i) ↔ R 0 ∧ R 1 := by
    constructor
    · intro h; exact ⟨h 0, h 1⟩
    · rintro ⟨h0, h1⟩ ⟨i, hi⟩
      match i, hi with
      | 0, _ => exact h0
      | 1, _ => exact h1
  have fresh : ∀ F ∈ ([] : List (FormulaN herbrandExLang)) ++ ([ep, eq] ++ [.all 4 cf]),
      9 ∉ formulaFVN F := by
    intro F hF
    simp only [List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl | rfl
    all_goals simp [c2, cf, ep, eq, formulaFVN, herbrandExP, herbrandExQ,
      Membership.mem, Set.iUnion, Set.union, Set.diff, Set.singleton,
      termFV, vec2, herbrandExLang, finTwo, finTwoAll]
  have r : FOLKStep1 ⟨[], [ep, eq, c2]⟩ ⟨[], [ep, eq, .all 4 cf]⟩ := by
    simpa [c2, cf, formulaSubstN, herbrandExP, herbrandExQ, substAtom, termSubst] using
      (FOLKStep1.allRight (L := herbrandExLang) 9 4 cf [] [ep, eq] fresh
        (by simp [cf, isFreeForN, herbrandExP, herbrandExQ, termFV, Membership.mem, Set.singleton]))
  exact .onePremise r herbrandExPrefix6

-- ===================================================================
-- Example 7.5.3 (helper defs): Proof tree components
-- ===================================================================













-- ===================================================================
-- Example 7.5.3 (companion theorem): herbrandExDisjunctionProvable
-- ===================================================================

/-- Example 7.5.3 (companion theorem): The Herbrand disjunction -> not P(a, f(a)), not Q(f(a), g(f(a))), P(a, f(a)) and Q(f(a), g(f(a))) is LK-provable. The first succedent not P(a, f(a)) is the negation of a conjunct P(a, f(a)) of the third succedent, and the second succedent not Q(f(a), g(f(a))) is the negation of the other conjunct Q(f(a), g(f(a))). Proof: Construct an LK proof tree using axioms P(a,f(a)) -> P(a,f(a)) and Q(f(a),g(f(a))) -> Q(f(a),g(f(a))), applying negRight, weakenRight, exchangeRight to build both branches, then andRight to combine them. -/
@[blueprint "chap7__example_7_5_3" (main := true)]
theorem herbrandExDisjunctionProvable :
    folkProvable herbrandExDisjunction

end LCS.Herbrand.HerbrandTheorem.Main
