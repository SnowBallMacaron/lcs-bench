import LCS.Item
import LCS.Util
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.FirstOrder.Gentzen.Hintikka
import Attach
import LCS.FirstOrder.Completeness.Basic.ProofsStamp

/-! # FirstOrder.Completeness.Basic
    Formalization of Chapter 5, Sections 5.5.1-5.5.3.
    Organizing terms, search procedure, and completeness of G
    for languages with function symbols and no equality.
    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.FirstOrder.Completeness

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.Gentzen.Hintikka

-- ATTACH-BLOCKER: unsupported untagged structure
/-- A finite list of term/formula records, finite availability lists, and
an activated-variable counter. -/
structure SearchState (L : Language) : Type 1 where
  /-- TERM0: list of (term, formulaList) pairs -/
  term0 : List (Term L × List (FormulaN L))
  /-- AVAIL_i: maps index i to the remaining available terms -/
  avail : Nat → List (Term L)
  /-- NUMACT: counter of activated new variables -/
  numact : Nat

-- ===================================================================
-- Theorem 5.5.1 (companion def): isFiniteSubsequent
-- ===================================================================

/-- Theorem 5.5.1 (finite subsequence): A finite list occurs in an ordered
possibly infinite sequence at strictly increasing positions. -/
@[blueprint "chap5__theorem_5_5_1"]
def IsFiniteSubsequenceN {L : Language} (xs : List (FormulaN L))
    (a : Nat → Option (FormulaN L)) : Prop :=
  ∃ pos : Fin xs.length → Nat,
    (∀ i j, i < j → pos i < pos j) ∧ ∀ i, a (pos i) = some xs[i]

/-- Theorem 5.5.1: A finite subsequent consists of finite subsequences of
the input's antecedent and succedent, preserving order and occurrences. -/
@[blueprint "chap5__theorem_5_5_1"]
def IsFiniteSubsequentInf {L : Language} (s : Sequent L) (q : InfSequentN L) : Prop :=
  IsFiniteSubsequenceN s.antecedent q.antecedent ∧
    IsFiniteSubsequenceN s.succedent q.succedent

-- retained: used by LCS.FirstOrder.Completeness.Search.Part2
/-- Finite embedding preserves the sequent-wide free/bound convention. -/
theorem crossNoFreeBoundInf_ofSequent_iff {L : Language} (s : Sequent L) :
    crossNoFreeBoundInf (InfSequentN.ofSequent s) ↔ crossNoFreeBound s := by
  simp only [crossNoFreeBoundInf, crossNoFreeBound,
    InfSequentN.memAntecedent_ofSequent, InfSequentN.memSuccedent_ofSequent,
    List.mem_append]

-- ===================================================================
-- Theorem 5.5.1 (companion def): searchHaltsConcrete
-- ===================================================================



-- ===================================================================
-- Example 5.5.1 (companion type): ExFuncAFG
-- ===================================================================

/-- Example 5.5.1 (companion): Function symbols for the TERMS enumeration
example language with binary function f and unary function g. -/
@[blueprint "chap5__example_5_5_1"]
inductive ExFuncAFG : Type where
  | f : ExFuncAFG
  | g : ExFuncAFG

-- ===================================================================
-- Example 5.5.1 (companion type): ExConstAFG
-- ===================================================================

/-- Example 5.5.1 (companion): Constant symbols for the TERMS enumeration
example language with one constant a. -/
@[blueprint "chap5__example_5_5_1"]
inductive ExConstAFG : Type where
  | a : ExConstAFG

-- ===================================================================
-- Example 5.5.1 (companion def): exLangAFG
-- ===================================================================

/-- Example 5.5.1: Language with one constant a, binary function f,
and unary function g, no predicate symbols. -/
@[blueprint "chap5__example_5_5_1"]
def exLangAFG : Language where
  funSymbols := ExFuncAFG
  funArity := fun
    | .f => 2
    | .g => 1
  constSymbols := ExConstAFG
  predSymbols := Empty
  predArity := Empty.elim
  hasEquality := false

-- ===================================================================
-- Example 5.5.1: exTermsEnumFuncSyms
-- ===================================================================

/-- Example 5.5.1 (companion): A concrete prefix of the TERMS enumeration for a
language with constant a, binary function f, and unary function g:
[a, g(a), f(a,a), g(g(a)), g(f(a,a)), f(g(a),a), f(a,g(a)),
f(g(a),g(a)), ...]. -/
@[blueprint "chap5__example_5_5_1"]
def exTermsEnumFuncSyms : List (Term exLangAFG) :=
  let a : Term exLangAFG := Term.const ExConstAFG.a
  let ga := Term.func ExFuncAFG.g (fun _ => a)
  let faa := Term.func ExFuncAFG.f (vec2 a a)
  let gga := Term.func ExFuncAFG.g (fun _ => ga)
  let gfaa := Term.func ExFuncAFG.g (fun _ => faa)
  let fgaa := Term.func ExFuncAFG.f (vec2 ga a)
  let faga := Term.func ExFuncAFG.f (vec2 a ga)
  let fgaga := Term.func ExFuncAFG.f (vec2 ga ga)
  [a, ga, faa, gga, gfaa, fgaa, faga, fgaga]

-- ===================================================================
-- Example 5.5.1 (companion def): exTerm0AFG
-- ===================================================================

/-- Example 5.5.1: TERM0 initialized as [(a, [])] -- a single record
with term a and empty formula list. -/
@[blueprint "chap5__example_5_5_1" (main := true)]
def exTerm0AFG :
    List (Term exLangAFG × List (FormulaN exLangAFG)) :=
  [(Term.const ExConstAFG.a, [])]

-- ===================================================================
-- Example 5.5.1 (companion def): exAvail0AFG
-- ===================================================================

/-- Example 5.5.1: The seven displayed AVAIL₀ entries are the tail of
the eight displayed TERMS entries. -/
@[blueprint "chap5__example_5_5_1"]
def exAvail0AFG : List (Term exLangAFG) :=
  exTermsEnumFuncSyms.tail

-- ===================================================================
-- Example 5.5.1 (companion def): exAvail1AFG
-- ===================================================================

/-- Example 5.5.1: The nine displayed AVAIL₁ terms, in order:
y₁, g(y₁), f(a,y₁), f(y₁,a), f(y₁,y₁), g(g(y₁)), g(f(a,y₁)),
g(f(y₁,a)), g(f(y₁,y₁)). The parity variable convention represents y₁
by variable index 3. -/
@[blueprint "chap5__example_5_5_1"]
def exAvail1AFG : List (Term exLangAFG) :=
  let a : Term exLangAFG := Term.const ExConstAFG.a
  let y1 : Term exLangAFG := Term.var 3
  let gy1 := Term.func ExFuncAFG.g (fun _ => y1)
  let fay1 := Term.func ExFuncAFG.f (vec2 a y1)
  let fy1a := Term.func ExFuncAFG.f (vec2 y1 a)
  let fy1y1 := Term.func ExFuncAFG.f (vec2 y1 y1)
  let ggy1 := Term.func ExFuncAFG.g (fun _ => gy1)
  let gfay1 := Term.func ExFuncAFG.g (fun _ => fay1)
  let gfy1a := Term.func ExFuncAFG.g (fun _ => fy1a)
  let gfy1y1 := Term.func ExFuncAFG.g (fun _ => fy1y1)
  [y1, gy1, fay1, fy1a, fy1y1, ggy1, gfay1, gfy1a, gfy1y1]

-- ===================================================================
-- Example 5.5.2 (companion type): ExPredPQf2
-- ===================================================================

/-- Example 5.5.2 (companion): Predicate symbols P and Q for the search
procedure proof example with function symbols. -/
@[blueprint "chap5__example_5_5_2"]
inductive ExPredPQf2 : Type where
  | P : ExPredPQf2
  | Q : ExPredPQf2

-- ===================================================================
-- Example 5.5.2 (companion type): ExFuncF2
-- ===================================================================

/-- Example 5.5.2 (companion): Function symbol f for the search procedure
proof example. -/
@[blueprint "chap5__example_5_5_2"]
inductive ExFuncF2 : Type where
  | f : ExFuncF2

-- ===================================================================
-- Example 5.5.2 (companion def): exLangPQf2
-- ===================================================================

/-- Example 5.5.2: Language with unary function f, no constants,
unary predicates P and Q. -/
@[blueprint "chap5__example_5_5_2"]
def exLangPQf2 : Language where
  funSymbols := ExFuncF2
  funArity := fun
    | .f => 1
  constSymbols := Empty
  predSymbols := ExPredPQf2
  predArity := fun
    | .P => 1
    | .Q => 1
  hasEquality := false

-- ===================================================================
-- Example 5.5.2 (companion def): exFormulaPQf2
-- ===================================================================

/-- Example 5.5.2: The formula (forall x P(x) and exists y Q(y)) implies
(P(f(v)) and exists z Q(z)), where P and Q are unary predicates, f is a unary function symbol. Variables: x = 0, y = 1, z = 2, v = 3. -/
@[blueprint "chap5__example_5_5_2"]
def exFormulaPQf2 : FormulaN exLangPQf2 :=
  let px := FormulaN.predN ExPredPQf2.P (fun _ => Term.var 0)
  let qy := FormulaN.predN ExPredPQf2.Q (fun _ => Term.var 1)
  let qz := FormulaN.predN ExPredPQf2.Q (fun _ => Term.var 2)
  let fv : Term exLangPQf2 :=
    Term.func ExFuncF2.f (fun _ => Term.var 3)
  let pfv := FormulaN.predN ExPredPQf2.P (fun _ => fv)
  FormulaN.impl
    (FormulaN.conj (FormulaN.all 0 px) (FormulaN.ex 1 qy))
    (FormulaN.conj pfv (FormulaN.ex 2 qz))

-- ===================================================================
-- Example 5.5.2 (companion def): exEigenvariableActivation
-- ===================================================================



-- ===================================================================
-- Example 5.5.3 (companion type): ExPredPQa
-- ===================================================================

/-- Example 5.5.3 (companion): Predicate symbols P and Q for the
counter-example search example with function symbols. -/
@[blueprint "chap5__example_5_5_3"]
inductive ExPredPQa : Type where
  | P : ExPredPQa
  | Q : ExPredPQa

-- ===================================================================
-- Example 5.5.3 (companion type): ExFuncFa
-- ===================================================================

/-- Example 5.5.3 (companion): Function symbol f for the counter-example
search example. -/
@[blueprint "chap5__example_5_5_3"]
inductive ExFuncFa : Type where
  | f : ExFuncFa

-- ===================================================================
-- Example 5.5.3 (companion type): ExConstA
-- ===================================================================

/-- Example 5.5.3 (companion): Constant symbol a for the counter-example
search example. -/
@[blueprint "chap5__example_5_5_3"]
inductive ExConstA : Type where
  | a : ExConstA

-- ===================================================================
-- Example 5.5.3 (companion def): exLangPQa
-- ===================================================================

/-- Example 5.5.3: Language with constant a, unary function f, and
unary predicates P and Q. -/
@[blueprint "chap5__example_5_5_3"]
def exLangPQa : Language where
  funSymbols := ExFuncFa
  funArity := fun
    | .f => 1
  constSymbols := ExConstA
  predSymbols := ExPredPQa
  predArity := fun
    | .P => 1
    | .Q => 1
  hasEquality := false

-- ===================================================================
-- Example 5.5.3 (companion def): exFormulaPQa
-- ===================================================================

/-- Example 5.5.3: The formula (exists x P(x) and Q(a)) implies
forall y P(f(y)). Variables: x = 0, y = 1. -/
@[blueprint "chap5__example_5_5_3"]
def exFormulaPQa : FormulaN exLangPQa :=
  let px := FormulaN.predN ExPredPQa.P (fun _ => Term.var 0)
  let qa := FormulaN.predN ExPredPQa.Q
    (fun _ => Term.const ExConstA.a)
  let fy : Term exLangPQa :=
    Term.func ExFuncFa.f (fun _ => Term.var 1)
  let pfy := FormulaN.predN ExPredPQa.P (fun _ => fy)
  FormulaN.impl
    (FormulaN.conj (FormulaN.ex 0 px) qa)
    (FormulaN.all 1 pfy)

-- ===================================================================
-- Example 5.5.3 (companion def): exFinishedNonclosedTree
-- ===================================================================

/-- Example 5.5.3: The top sequent P(y2), Q(a) -> P(f(y1)) which is
finished (all atomic) but nonclosed. -/
@[blueprint "chap5__example_5_5_3"]
def exFinishedNonclosedTree : Sequent exLangPQa :=
  let y1 : Term exLangPQa := Term.var 3
  let y2 : Term exLangPQa := Term.var 5
  let py2 := FormulaN.predN ExPredPQa.P (fun _ => y2)
  let qa := FormulaN.predN ExPredPQa.Q
    (fun _ => Term.const ExConstA.a)
  let fy1 := Term.func ExFuncFa.f (fun _ => y1)
  let pfy1 := FormulaN.predN ExPredPQa.P (fun _ => fy1)
  Sequent.mk [py2, qa] [pfy1]

-- ===================================================================
-- Example 5.5.3 (companion def): exCounterDomainH
-- ===================================================================

/-- Example 5.5.3: The counter-example domain H = {a, f^n(a), y1, f^n(y1),
y2, f^n(y2), ...} formed from all terms in TERM0 and activated AVAILi. Defined as a predicate on Term exLangPQa recognizing terms built from a, y1, y2 under applications of f. -/
@[blueprint "chap5__example_5_5_3"]
def exCounterDomainH : Set (Term exLangPQa) :=
  fun t =>
    -- t is in H if it is built from {a, y1, y2} under f
    ∃ (base : Term exLangPQa) (n : Nat),
      (base = Term.const ExConstA.a ∨
       base = Term.var 3 ∨
       base = Term.var 5) ∧
      t = Nat.recOn n base (fun _ acc =>
        Term.func ExFuncFa.f (fun _ => acc))

/-- Example 5.5.3: The constant a belongs to H. -/
@[blueprint "chap5__example_5_5_3"]
theorem exCounterDomainH_const : exCounterDomainH (Term.const ExConstA.a) 

/-- Example 5.5.3: The first activated variable y₁ belongs to H. -/
@[blueprint "chap5__example_5_5_3"]
theorem exCounterDomainH_y1 : exCounterDomainH (Term.var 3) 

/-- Example 5.5.3: The second activated variable y₂ belongs to H. -/
@[blueprint "chap5__example_5_5_3"]
theorem exCounterDomainH_y2 : exCounterDomainH (Term.var 5) 

/-- Example 5.5.3: H is closed under its unary function f. -/
@[blueprint "chap5__example_5_5_3"]
theorem exCounterDomainH_func (t : Term exLangPQa) (ht : exCounterDomainH t) :
    exCounterDomainH (Term.func ExFuncFa.f (fun _ => t)) 

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Example 5.5.3: The structure on H interprets f and a as term
constructors, P as true exactly at y₂, and Q as true exactly at a.
The odd-index supply represents y₁ by 3 and y₂ by 5. -/
def exCounterInterp : Structure exLangPQa where
  carrier := {t : Term exLangPQa // exCounterDomainH t}
  carrierNonempty := ⟨⟨Term.const ExConstA.a, exCounterDomainH_const⟩⟩
  interpFunc
    | ExFuncFa.f, args =>
      ⟨Term.func ExFuncFa.f (fun _ => (args ⟨0, by decide⟩).val),
        exCounterDomainH_func _ (args ⟨0, by decide⟩).property⟩
  interpConst
    | ExConstA.a => ⟨Term.const ExConstA.a, exCounterDomainH_const⟩
  interpPred
    | ExPredPQa.P, args => (args ⟨0, by decide⟩).val = Term.var 5
    | ExPredPQa.Q, args => (args ⟨0, by decide⟩).val = Term.const ExConstA.a





/-- Example 5.5.3: A structure on H with arbitrary unary predicates P and Q.
The constant a and unary function f retain their term-constructor interpretations;
y₁ and y₂ are the domain elements represented by variable indices 3 and 5. -/
@[blueprint "chap5__example_5_5_3"]
def exCounterInterpWith
    (p q : {t : Term exLangPQa // exCounterDomainH t} → Prop) :
    Structure exLangPQa :=
  { exCounterInterp with
    carrierNonempty := ⟨⟨Term.const ExConstA.a, exCounterDomainH_const⟩⟩
    interpPred := fun
      | ExPredPQa.P, args => p (args ⟨0, by decide⟩)
      | ExPredPQa.Q, args => q (args ⟨0, by decide⟩) }

/-- Example 5.5.3: Every predicate completion on H with P(y₂), Q(a),
and ¬P(f(y₁)) falsifies A under every assignment and falsifies → A.
The other predicate values are arbitrary. -/
@[blueprint "chap5__example_5_5_3" (main := true)]
theorem exCounterInterpWith_falsifies
    (p q : {t : Term exLangPQa // exCounterDomainH t} → Prop)
    (hP : p ⟨Term.var 5, exCounterDomainH_y2⟩)
    (hQ : q ⟨Term.const ExConstA.a, exCounterDomainH_const⟩)
    (hPf : ¬ p ⟨Term.func ExFuncFa.f (fun _ => Term.var 3),
      exCounterDomainH_func _ exCounterDomainH_y1⟩)
    (as : Assignment (exCounterInterpWith p q)) :
    ¬ formulaEvalN (exCounterInterpWith p q) exFormulaPQa as ∧
      sequentFalsifiableIn (exCounterInterpWith p q) (Sequent.mk [] [exFormulaPQa]) 

-- ===================================================================
-- sequentFalsifiable: Falsifiability for Sequent
-- ===================================================================

/-- Theorem 5.5.1 (companion): A sequent, for any equality flag, is falsifiable
iff some structure and assignment make all antecedent formulae true and all
succedent formulae false. -/
@[blueprint "chap5__lemma_5_6_2"]
def sequentFalsifiable {L : Language} (seq : Sequent L) : Prop :=
  ∃ (M : Structure L) (s : Assignment M),
    (∀ A ∈ seq.antecedent, formulaEvalN M A s) ∧
    (∀ B ∈ seq.succedent, ¬ formulaEvalN M B s)



/-- Definition 5.4.2 (i): A sequent over a language without equality is
falsifiable iff some structure and assignment make all antecedent formulae
true and all succedent formulae false. -/
@[blueprint "chap5__definition_5_4_2" (main := true)]
def sequentFalsifiableNoEq {L : Language} (hL : L.withoutEquality)
    (s : Sequent L) : Prop :=
  sequentFalsifiable s

end LCS.FirstOrder.Completeness
