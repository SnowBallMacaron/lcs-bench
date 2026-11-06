import LCS.Item
import LCS.Util
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.SignedFormulae
import Attach
import LCS.FirstOrder.Gentzen.Hintikka.HintikkaSets.ProofsStamp

/-! # Hintikka sets (Section 5.4.6)

The free/bound variable convention obtained from Lemma 5.3.4, Definition 5.4.7
(Hintikka sets over a language without equality) and Lemma 5.4.5 (every
Hintikka set is satisfiable in the structure H_S with domain H).
Source: Logic for Computer Science, Gallier 2015
-/

section
namespace LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.SyntaxN.Variables

-- ===================================================================
-- Per-formula free/bound condition: noFreeBound
-- ===================================================================

-- retained: used by LCS.FirstOrder.Completeness, LCS.FirstOrder.Completeness.Basic, LCS.FirstOrder.Gentzen.Hintikka.Construction, LCS.FirstOrder.Gentzen.Hintikka.SearchClosure
/-- Per-formula condition, used by chapter 6 statements pending E-CUTFB repair.
Each formula separately has disjoint sets of free and bound variables. -/
def noFreeBound {L : Language} (seq : Sequent L) : Prop :=
  ∀ A ∈ (seq.antecedent ++ seq.succedent),
    ∀ x : Nat, ¬(x ∈ formulaFVN A ∧ x ∈ formulaBVN A)

/-- Theorem 5.4.1 (required helper): Cross-formula free/bound
disjointness — the §5.4.7-preamble standing assumption:
"the set of all variables occurring free in some formula in the sequent
is disjoint from the set of all variables occurring bound in some formula
in the sequent" (textbook §5.4.7 line 4, "we can assume that ..."
via L5.3.4). Used as the hypothesis "no free variable occurs bound"
of Thm 5.4.1 (§5.4.7 line 359) and re-used in §5.4.6/§5.5.1/§5.6.1
under the same L5.3.4 justification. -/
@[blueprint "chap5__definition_5_4_9"]
def crossNoFreeBound {L : Language} (seq : Sequent L) : Prop :=
  ∀ x : Nat,
    (∃ A ∈ (seq.antecedent ++ seq.succedent), x ∈ formulaFVN A) →
    (∀ B ∈ (seq.antecedent ++ seq.succedent), x ∉ formulaBVN B)

/-- The §5.5 set-wide convention separates all free variables of Γ from all
its bound variables, as required for model existence from consistency. -/
@[blueprint "chap5__definition_5_5_1"]
def setCrossNoFreeBound {L : Language} (Γ : Set (FormulaN L)) : Prop :=
  ∀ x, (∃ A ∈ Γ, x ∈ formulaFVN A) → ∀ B ∈ Γ, x ∉ formulaBVN B

-- retained: used by LCS.CutElim.CompletenessBridge, LCS.FirstOrder.Completeness, LCS.FirstOrder.Completeness.Basic, LCS.FirstOrder.Equality.Completeness.Part1, LCS.FirstOrder.Gentzen.Hintikka.Construction, LCS.FirstOrder.Gentzen.Hintikka.SearchClosure
/-- No formula in the sequent contains eq_.

UNFAITHFUL — TO REMOVE: the textbook encodes "language without
equality" directly via the `hasEquality` field on `Language`
(Def 5.2.1) — setting `L.hasEquality = false` makes `FormulaN.eq_`
uninhabited, so any `seq : Sequent L` automatically contains no eq_.
This `seqNoEq` predicate is Lean-specific proof-helper scaffolding
for the unfaithful Thm 5.5.1; remove together with it. -/
def seqNoEq {L : Language} (seq : Sequent L) : Prop :=
  (∀ A ∈ seq.antecedent, formulaNoEq A) ∧
  (∀ B ∈ seq.succedent, formulaNoEq B)

-- ===================================================================
-- Closure lemmas: decomposition preserves formula-level properties
-- ===================================================================

-- formulaSubstN_noEq is imported from SemanticsN

-- ===================================================================
-- IsHintikkaSet: Hintikka sets over normalized signed formulae
-- ===================================================================

/-- Definition 5.4.7: A Hintikka set S over FormulaN with respect to a term
algebra H over the occurrence language L_S satisfies conditions H0-H6.
The language parameter fixes the absence of equality. -/
@[blueprint "chap5__definition_5_4_7" (main := true)]
structure IsHintikkaSet (L : Language) (hL : L.withoutEquality) (H : Set (Term L))
    (S : Set (SignedFormula L)) : Prop where
  /-- H is a term algebra over the symbols occurring in S. -/
  hTA : IsTermAlgebraOver L S H
  /-- H0: No atomic formula and its conjugate are both in S -/
  h0 : ∀ (A : FormulaN L), A.isAtomic = true →
    ¬(SignedFormula.trueF A ∈ S ∧ SignedFormula.falseF A ∈ S)
  /-- H1: If a type-A formula is in S, then both components are in S -/
  h1 : ∀ (a : TypeA L), a.toSigned ∈ S → a.comp1 ∈ S ∧ a.comp2 ∈ S
  /-- H2: If a type-B formula is in S, then at least one component is in S -/
  h2 : ∀ (b : TypeB L), b.toSigned ∈ S → b.comp1 ∈ S ∨ b.comp2 ∈ S
  /-- H3: Every free-for component C(t), for t in H, belongs to S.
  The required free-for evidence is provided by H6. -/
  h3 : ∀ (c : TypeC L), c.toSigned ∈ S →
    ∀ (t : Term L), t ∈ H → ∀ h : isFreeForN t c.var c.body, c.comp t h ∈ S
  /-- H4: A type-D formula in S has a free-for witness t in H with D(t) in S. -/
  h4 : ∀ (d : TypeD L), d.toSigned ∈ S →
    ∃ (t : Term L), t ∈ H ∧ ∃ h : isFreeForN t d.var d.body, d.comp t h ∈ S
  /-- H5: Every variable occurring free in some formula of S is in H -/
  h5 : ∀ (sf : SignedFormula L), sf ∈ S →
    ∀ (x : Nat), x ∈ signedFormulaFreeVars sf → Term.var x ∈ H
  /-- H6: isFreeFor holds for quantified formulae in S -/
  h6 : ∀ (x : Nat) (A : FormulaN L) (t : Term L), t ∈ H →
    (SignedFormula.trueF (.all x A) ∈ S ∨
     SignedFormula.falseF (.all x A) ∈ S ∨
     SignedFormula.trueF (.ex x A) ∈ S ∨
     SignedFormula.falseF (.ex x A) ∈ S) →
    isFreeForN t x A

/-- Equality atoms cannot be formed in the language of a Hintikka set. -/
theorem IsHintikkaSet.hNoEq {L : Language} {hL : L.withoutEquality}
    {H : Set (Term L)} {S : Set (SignedFormula L)}
    (_hHS : IsHintikkaSet L hL H S) (hEq : L.hasEquality = true) (t1 t2 : Term L) :
    SignedFormula.trueF (FormulaN.eq_ hEq t1 t2) ∉ S ∧
      SignedFormula.falseF (FormulaN.eq_ hEq t1 t2) ∉ S := by
  have hFalse : L.hasEquality = false := hL
  simp [hFalse] at hEq

-- ===================================================================
-- Lemma 5.4.5 (normalized companion): hintikkaStructure
-- ===================================================================

/-- Lemma 5.4.5 (companion): The term-algebra carrier of a Hintikka set is nonempty. -/
theorem hintikkaStructure_carrierNonempty {L : Language} {hL : L.withoutEquality}
    {H : Set (Term L)} {S : Set (SignedFormula L)}
    (hHS : IsHintikkaSet L hL H S) : Nonempty { t : Term L // t ∈ H } := by
  obtain ⟨t, ht⟩ := hHS.hTA.nonempty
  exact ⟨⟨t, ht⟩⟩

/-- Lemma 5.4.5 (companion): The structure on H interprets symbols of L_S
by term formation. Other function and constant symbols denote a fixed member
of H. A predicate atom is false exactly when its negative signed atom belongs
to S; positive and unmentioned atoms are true, including predicates of rank zero. -/
@[blueprint "chap5__lemma_5_4_5"]
noncomputable def hintikkaStructure {L : Language} {hL : L.withoutEquality}
    (H : Set (Term L)) (S : Set (SignedFormula L))
    (hHS : IsHintikkaSet L hL H S) : Structure L := by
  classical
  exact {
    carrier := { t : Term L // t ∈ H }
    carrierNonempty := hintikkaStructure_carrierNonempty hHS
    interpFunc := fun f ts => if hf : f ∈ signedSetFunSyms S then
      ⟨Term.func f (fun i => (ts i).val),
        hHS.hTA.closedFunc f hf _ (fun i => (ts i).property)⟩
      else ⟨hHS.hTA.nonempty.choose, hHS.hTA.nonempty.choose_spec⟩
    interpConst := fun c => if hc : c ∈ signedSetConstSyms S then
      ⟨Term.const c, hHS.hTA.closedConst c hc⟩
      else ⟨hHS.hTA.nonempty.choose, hHS.hTA.nonempty.choose_spec⟩
    interpPred := fun P ts =>
      SignedFormula.falseF (FormulaN.predN P (fun i => (ts i).val)) ∉ S }

/-- Lemma 5.4.5 (companion): Variables represented in H denote themselves;
other variables denote the fixed member of the nonempty carrier. -/
@[blueprint "chap5__lemma_5_4_5"]
noncomputable def identityAssignment {L : Language} {hL : L.withoutEquality}
    (H : Set (Term L)) (S : Set (SignedFormula L))
    (hHS : IsHintikkaSet L hL H S) : Assignment (hintikkaStructure H S hHS) :=
  open Classical in
  fun x => if h : Term.var x ∈ H then ⟨Term.var x, h⟩
    else ⟨hHS.hTA.nonempty.choose, hHS.hTA.nonempty.choose_spec⟩

-- retained: used by LCS.FirstOrder.Equality.Part2
/-- A term over L_S whose free variables belong to H belongs to H. -/
theorem termInHOver {L : Language} {H : Set (Term L)} {S : Set (SignedFormula L)}
    (hTA : IsTermAlgebraOver L S H) (t : Term L)
    (hsyms : termFunSyms t ⊆ signedSetFunSyms S ∧ termConstSyms t ⊆ signedSetConstSyms S)
    (hvars : ∀ x, x ∈ termFV t → Term.var x ∈ H) : t ∈ H := by
  induction t with
  | var x => exact hvars x rfl
  | const c => exact hTA.closedConst c (hsyms.2 c List.mem_cons_self)
  | func f ts ih =>
    apply hTA.closedFunc f (hsyms.1 f (Or.inl rfl)) ts
    intro i
    apply ih i
    · exact ⟨fun g hg => hsyms.1 g (Or.inr ⟨i, hg⟩),
        fun c hc => hsyms.2 c ((termConstSyms_func_iff f ts c).mpr ⟨i, hc⟩)⟩
    · exact fun x hx => hvars x ⟨i, hx⟩

-- retained: used by LCS.FirstOrder.Completeness.MetaTheorems
/-- Lemma 5.4.5 (companion): A term in H evaluates to itself when its free
variables are represented in H. -/
theorem termEvalIdentity {L : Language} {hL : L.withoutEquality} {H : Set (Term L)}
    {S : Set (SignedFormula L)} {hHS : IsHintikkaSet L hL H S}
    (t : Term L) (ht : t ∈ H) (hvars : ∀ x, x ∈ termFV t → Term.var x ∈ H) :
    termEval (hintikkaStructure H S hHS) (identityAssignment H S hHS) t =
      ⟨t, ht⟩ := by
  induction t with
  | var x =>
    simp only [termEval, identityAssignment]
    exact dif_pos ht
  | const c =>
    have hc := (hHS.hTA.symbols (.const c) ht).2 c List.mem_cons_self
    simp only [termEval, hintikkaStructure]
    exact dif_pos hc
  | func f ts ih =>
    have hsyms := hHS.hTA.symbols (.func f ts) ht
    have hf := hsyms.1 f (Or.inl rfl)
    let args := fun i => termEval (hintikkaStructure H S hHS) (identityAssignment H S hHS) (ts i)
    have hstep : (hintikkaStructure H S hHS).interpFunc f args =
        (⟨Term.func f (fun i => (args i).val),
          hHS.hTA.closedFunc f hf _ (fun i => (args i).property)⟩ : { t : Term L // t ∈ H }) :=
      dif_pos hf
    change (hintikkaStructure H S hHS).interpFunc f args = _
    rw [hstep]
    apply Subtype.ext
    apply congrArg (Term.func f)
    funext i
    have hvars_i : ∀ x, x ∈ termFV (ts i) → Term.var x ∈ H := fun x hx => hvars x ⟨i, hx⟩
    have hti : ts i ∈ H := termInHOver hHS.hTA (ts i)
      ⟨fun g hg => hsyms.1 g (Or.inr ⟨i, hg⟩),
       fun c hc => hsyms.2 c ((termConstSyms_func_iff f ts c).mpr ⟨i, hc⟩)⟩ hvars_i
    exact congrArg Subtype.val (ih i hti hvars_i)

-- retained: used by LCS.FirstOrder.Equality.Part2
/-- Every argument of a signed predicate atom in S uses only symbols of S. -/
theorem predicateArgument_symbols {L : Language} {S : Set (SignedFormula L)}
    (P : L.predSymbols) (ts : Fin (L.predArity P) → Term L)
    (hmem : SignedFormula.trueF (.predN P ts) ∈ S ∨ SignedFormula.falseF (.predN P ts) ∈ S)
    (i : Fin (L.predArity P)) :
    termFunSyms (ts i) ⊆ signedSetFunSyms S ∧ termConstSyms (ts i) ⊆ signedSetConstSyms S := by
  constructor
  · intro f hf
    rcases hmem with h | h
    · exact ⟨.trueF (.predN P ts), h, i, hf⟩
    · exact ⟨.falseF (.predN P ts), h, i, hf⟩
  · intro c hc
    have hConst : c ∈ formulaConstSymsN (.predN P ts) := by
      change Term.const c ∈ formulaConstsList (.predN P ts)
      simp only [formulaConstsList, ← List.flatMap_eq_foldl, List.mem_flatMap, List.mem_ofFn]
      exact ⟨i, ⟨i, rfl⟩, hc⟩
    rcases hmem with h | h
    · exact ⟨.trueF (.predN P ts), h, hConst⟩
    · exact ⟨.falseF (.predN P ts), h, hConst⟩

-- ===================================================================
-- Lemma 5.4.5 (normalized companion): formulaDepth
-- ===================================================================

-- retained: used by LCS.FirstOrder.Equality.Part2
/-- Lemma 5.4.5 (normalized companion): FormulaN depth: counts connective
and quantifier layers. Atomic formulae (predN, eq_) have depth 0. Used for
well-founded induction in the Hintikka set satisfiability proof. -/
def formulaDepth {L : Language} : FormulaN L → Nat
  | .predN _ _ => 0
  | .eq_ _ _ _ => 0
  | .neg A => 1 + formulaDepth A
  | .conj A B => 1 + formulaDepth A + formulaDepth B
  | .disj A B => 1 + formulaDepth A + formulaDepth B
  | .impl A B => 1 + formulaDepth A + formulaDepth B
  | .all _ A => 1 + formulaDepth A
  | .ex _ A => 1 + formulaDepth A

-- retained: used by LCS.FirstOrder.Equality.Part2
/-- Substitution preserves formula depth for FormulaN. -/
theorem formulaSubstN_depth {L : Language}
    (A : FormulaN L) (t : Term L) (x : Nat) :
    formulaDepth (formulaSubstN A t x) = formulaDepth A := by
-- BEGIN PROOF
  induction A with
  | predN _ _ => rfl
  | eq_ _ _ _ => rfl
  | neg A ih => simp [formulaSubstN, formulaDepth, ih]
  | conj A B ihA ihB => simp [formulaSubstN, formulaDepth, ihA, ihB]
  | disj A B ihA ihB => simp [formulaSubstN, formulaDepth, ihA, ihB]
  | impl A B ihA ihB => simp [formulaSubstN, formulaDepth, ihA, ihB]
  | all y A ih =>
    simp only [formulaSubstN]; split
    · simp only [formulaDepth]; omega
    · rfl
  | ex y A ih =>
    simp only [formulaSubstN]; split
    · simp only [formulaDepth]; omega
    · rfl

-- ===================================================================
-- Lemma 5.4.5 (normalized): Hintikka set satisfiability for FormulaN
-- ===================================================================

-- retained: used by LCS.FirstOrder.Equality.Part2
/-- Substitution at an occurring variable introduces every free variable of its term. -/
theorem termFV_subst_contains {L : Language} (r t : Term L) (x v : Nat)
    (hx : x ∈ termFV r) (hv : v ∈ termFV t) : v ∈ termFV (termSubst r t x) := by
  induction r with
  | var y =>
    have hxy : x = y := hx
    subst y
    simpa [termSubst] using hv
  | const _ => exact hx.elim
  | func f ts ih =>
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, ih i hi⟩

-- retained: used by LCS.FirstOrder.Equality.Part2
/-- Free-for substitution preserves the inserted term's free variables when
the substituted variable occurs freely in the formula. -/
theorem formulaFVN_subst_contains {L : Language} (A : FormulaN L) (t : Term L)
    (x v : Nat) (hfree : isFreeForN t x A) (hx : x ∈ formulaFVN A)
    (hv : v ∈ termFV t) : v ∈ formulaFVN (formulaSubstN A t x) := by
  induction A with
  | predN P ts =>
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, termFV_subst_contains (ts i) t x v hi hv⟩
  | eq_ h r u =>
    rcases hx with hx | hx
    · exact Or.inl (termFV_subst_contains r t x v hx hv)
    · exact Or.inr (termFV_subst_contains u t x v hx hv)
  | neg A ih => exact ih hfree hx
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
    rcases hx with hx | hx
    · exact Or.inl (ihA hfree.1 hx)
    · exact Or.inr (ihB hfree.2 hx)
  | all y A ih | ex y A ih =>
    have hxy : x ≠ y := hx.2
    have hf := hfree.resolve_left hxy
    simp only [formulaSubstN, bne_iff_ne, if_pos hxy, formulaFVN]
    refine ⟨ih hf.2 hx.1, ?_⟩
    intro hvy
    have hvy' : v = y := hvy
    exact hf.1 (hvy' ▸ hv)

-- retained: used by LCS.FirstOrder.Completeness.MetaTheorems
/-- Substitution in a signed member of S evaluates using the term itself as
a carrier element. H5 supplies its variables when substitution is nonvacuous. -/
theorem hintikkaSubstEval {L : Language} {hL : L.withoutEquality}
    {H : Set (Term L)} {S : Set (SignedFormula L)} (hHS : IsHintikkaSet L hL H S)
    (A : FormulaN L) (t : Term L) (x : Nat) (ht : t ∈ H)
    (hfree : isFreeForN t x A)
    (hmem : SignedFormula.trueF (formulaSubstN A t x) ∈ S ∨
      SignedFormula.falseF (formulaSubstN A t x) ∈ S) :
    formulaEvalN (hintikkaStructure H S hHS) (formulaSubstN A t x)
        (identityAssignment H S hHS) ↔
      formulaEvalN (hintikkaStructure H S hHS) A
        (assignUpdate (identityAssignment H S hHS) x ⟨t, ht⟩) := by
  classical
  refine (formulaSubstEvalDirectN (identityAssignment H S hHS) A t x hfree).trans ?_
  by_cases hx : x ∈ formulaFVN A
  · have hvars : ∀ v, v ∈ termFV t → Term.var v ∈ H := by
      intro v hv
      have hsub := formulaFVN_subst_contains A t x v hfree hx hv
      rcases hmem with h | h
      · exact hHS.h5 (.trueF (formulaSubstN A t x)) h v hsub
      · exact hHS.h5 (.falseF (formulaSubstN A t x)) h v hsub
    rw [termEvalIdentity t ht hvars]
  · apply coincidenceLemmaN
    intro y hy
    have hyx : y ≠ x := fun h => hx (h ▸ hy)
    simp [assignUpdate, hyx]

-- retained: used by LCS.FirstOrder.Completeness.MetaTheorems
/-- Lemma 5.4.5 (companion, normalized concrete): Satisfaction holds for the
specific hintikkaStructure and identityAssignment. Proved by
well-founded induction on formulaDepth with 8 cases (predN, eq_,
neg, conj, disj, impl, all, ex). -/
theorem hintikka_set_satisfiable_concrete {L : Language} (hL : L.withoutEquality)
    (H : Set (Term L)) (S : Set (SignedFormula L))
    (hHS : IsHintikkaSet L hL H S) :
    ∀ sf, sf ∈ S → SignedFormula.satisfiedBy
      (hintikkaStructure H S hHS) (identityAssignment H S hHS) sf := by
-- BEGIN PROOF
  let M := hintikkaStructure H S hHS
  let s := identityAssignment H S hHS
  -- Auxiliary lemma: predN case, used in both base and step cases.
  have predN_case : ∀ (P : L.predSymbols) (ts : Fin (L.predArity P) → Term L),
      (SignedFormula.trueF (.predN P ts) ∈ S →
        formulaEvalN M (.predN P ts) s) ∧
      (SignedFormula.falseF (.predN P ts) ∈ S →
        ¬ formulaEvalN M (.predN P ts) s) := by
    intro P ts; constructor
    · -- H0 excludes the negative atom when the positive atom belongs to S.
      intro hT
      show M.interpPred P (fun i => termEval M s (ts i))
      have htsH : ∀ i, ts i ∈ H := fun i =>
        termInHOver hHS.hTA (ts i) (predicateArgument_symbols P ts (Or.inl hT) i)
          (fun x hx => hHS.h5 (.trueF (.predN P ts)) hT x ⟨i, hx⟩)
      have heval : ∀ i, termEval M s (ts i) = ⟨ts i, htsH i⟩ :=
        fun i => termEvalIdentity (ts i) (htsH i)
          (fun x hx => hHS.h5 (.trueF (.predN P ts)) hT x ⟨i, hx⟩)
      show hintikkaStructure H S hHS |>.interpPred P (fun i => termEval M s (ts i))
      simp only [hintikkaStructure]
      have : (fun i => (termEval M s (ts i)).val) = ts := by
        funext i; exact congrArg Subtype.val (heval i)
      rw [this]
      exact fun hF => hHS.h0 (.predN P ts) rfl ⟨hT, hF⟩
    · -- A negative atom in S is false by the predicate interpretation.
      intro hF heval
      have htsH : ∀ i, ts i ∈ H := fun i =>
        termInHOver hHS.hTA (ts i) (predicateArgument_symbols P ts (Or.inr hF) i)
          (fun x hx => hHS.h5 (.falseF (.predN P ts)) hF x ⟨i, hx⟩)
      have heval' : ∀ i, termEval M s (ts i) = ⟨ts i, htsH i⟩ :=
        fun i => termEvalIdentity (ts i) (htsH i)
          (fun x hx => hHS.h5 (.falseF (.predN P ts)) hF x ⟨i, hx⟩)
      have hNotFalse : SignedFormula.falseF (.predN P ts) ∉ S := by
        have : hintikkaStructure H S hHS |>.interpPred P
            (fun i => termEval M s (ts i)) := heval
        simp only [hintikkaStructure] at this
        have heq : (fun i => (termEval M s (ts i)).val) = ts := by
          funext i; exact congrArg Subtype.val (heval' i)
        rwa [heq] at this
      exact hNotFalse hF
  -- Key claim proved by well-founded induction on formulaDepth.
  -- We use formulaDepth rather than structural induction because the
  -- quantifier cases require the claim for formulaSubstN A t x, which
  -- has the same formula depth as A (by formulaSubstN_depth).
  have key : ∀ A : FormulaN L,
      (SignedFormula.trueF A ∈ S → formulaEvalN M A s) ∧
      (SignedFormula.falseF A ∈ S → ¬ formulaEvalN M A s) := by
    -- Strong induction on formulaDepth via an auxiliary indexed by Nat.
    suffices aux : ∀ (n : Nat) (A : FormulaN L), formulaDepth A ≤ n →
        (SignedFormula.trueF A ∈ S → formulaEvalN M A s) ∧
        (SignedFormula.falseF A ∈ S → ¬ formulaEvalN M A s) from
      fun A => aux (formulaDepth A) A (Nat.le_refl _)
    intro n; induction n with
    | zero =>
      -- Base case: depth 0 means A is atomic (predN or eq_).
      intro A hle
      match A with
      | .predN P ts => exact predN_case P ts
      | .eq_ hL t1 t2 =>
        exact ⟨fun hT => absurd hT (hHS.hNoEq hL t1 t2).1,
               fun hF => absurd hF (hHS.hNoEq hL t1 t2).2⟩
      | .neg _ => simp [formulaDepth] at hle
      | .conj _ _ => simp [formulaDepth] at hle
      | .disj _ _ => simp [formulaDepth] at hle
      | .impl _ _ => simp [formulaDepth] at hle
      | .all _ _ => simp [formulaDepth] at hle
      | .ex _ _ => simp [formulaDepth] at hle
    | succ n ih_n =>
      intro A hle
      match A with
      -- Atomic cases (depth 0) are handled identically to the zero case:
      | .predN P ts => exact predN_case P ts
      | .eq_ hL t1 t2 =>
        exact ⟨fun hT => absurd hT (hHS.hNoEq hL t1 t2).1,
               fun hF => absurd hF (hHS.hNoEq hL t1 t2).2⟩
      -- Connective cases use the IH at strictly smaller depth:
      | .conj A' B' =>
        have ihA := ih_n A' (by simp [formulaDepth] at hle; omega)
        have ihB := ih_n B' (by simp [formulaDepth] at hle; omega)
        exact ⟨fun hT => ⟨ihA.1 ((hHS.h1 (TypeA.tConj A' B') hT).1),
                            ihB.1 ((hHS.h1 (TypeA.tConj A' B') hT).2)⟩,
               fun hF ⟨ha, hb⟩ => (hHS.h2 (TypeB.fConj A' B') hF).elim
                 (fun hA => ihA.2 hA ha) (fun hB => ihB.2 hB hb)⟩
      | .disj A' B' =>
        have ihA := ih_n A' (by simp [formulaDepth] at hle; omega)
        have ihB := ih_n B' (by simp [formulaDepth] at hle; omega)
        exact ⟨fun hT => (hHS.h2 (TypeB.tDisj A' B') hT).elim
                 (fun hA => Or.inl (ihA.1 hA)) (fun hB => Or.inr (ihB.1 hB)),
               fun hF h => by
                 obtain ⟨hA, hB⟩ := hHS.h1 (TypeA.fDisj A' B') hF
                 cases h with
                 | inl ha => exact ihA.2 hA ha
                 | inr hb => exact ihB.2 hB hb⟩
      | .impl A' B' =>
        have ihA := ih_n A' (by simp [formulaDepth] at hle; omega)
        have ihB := ih_n B' (by simp [formulaDepth] at hle; omega)
        exact ⟨fun hT ha => (hHS.h2 (TypeB.tImpl A' B') hT).elim
                 (fun hFA => absurd ha (ihA.2 hFA)) (fun hTB => ihB.1 hTB),
               fun hF h => ihB.2 ((hHS.h1 (TypeA.fImpl A' B') hF).2)
                 (h (ihA.1 ((hHS.h1 (TypeA.fImpl A' B') hF).1)))⟩
      | .neg A' =>
        have ihA := ih_n A' (by simp [formulaDepth] at hle; omega)
        exact ⟨fun hT => ihA.2 (hHS.h1 (TypeA.tNeg A') hT).1,
               fun hF heval => heval (ihA.1 (hHS.h1 (TypeA.fNeg A') hF).1)⟩
      -- Quantifier cases: the IH applies to formulaSubstN A' t x since
      -- formulaSubstN_depth gives depth(A'[t/x]) = depth(A') ≤ n < n+1.
      | .all x A' =>
        constructor
        · -- True case: trueF (.all x A') ∈ S → ∀ a, eval (assignUpdate s x a) A'
          intro hT ⟨t, ht⟩
          have hfree : isFreeForN t x A' := hHS.h6 x A' t ht (Or.inl hT)
          have hsubst_in_S := hHS.h3 (TypeC.tAll x A') hT t ht hfree
          have hdepth_sub : formulaDepth (formulaSubstN A' t x) ≤ n := by
            rw [formulaSubstN_depth]; simp [formulaDepth] at hle; omega
          have heval_subst := (ih_n (formulaSubstN A' t x) hdepth_sub).1 hsubst_in_S
          exact (hintikkaSubstEval hHS A' t x ht hfree (Or.inl hsubst_in_S)).mp heval_subst
        · -- False case: falseF (.all x A') ∈ S → ¬ ∀ a, eval (assignUpdate s x a) A'
          intro hF hall
          obtain ⟨t, ht, hfree, hsubst_in_S⟩ := hHS.h4 (TypeD.fAll x A') hF
          have hdepth_sub : formulaDepth (formulaSubstN A' t x) ≤ n := by
            rw [formulaSubstN_depth]; simp [formulaDepth] at hle; omega
          have hneval := (ih_n (formulaSubstN A' t x) hdepth_sub).2 hsubst_in_S
          apply hneval
          exact (hintikkaSubstEval hHS A' t x ht hfree (Or.inr hsubst_in_S)).mpr (hall ⟨t, ht⟩)
      | .ex x A' =>
        constructor
        · -- True case: trueF (.ex x A') ∈ S → ∃ a, eval (assignUpdate s x a) A'
          intro hT
          obtain ⟨t, ht, hfree, hsubst_in_S⟩ := hHS.h4 (TypeD.tEx x A') hT
          have hdepth_sub : formulaDepth (formulaSubstN A' t x) ≤ n := by
            rw [formulaSubstN_depth]; simp [formulaDepth] at hle; omega
          have heval_subst := (ih_n (formulaSubstN A' t x) hdepth_sub).1 hsubst_in_S
          exact ⟨⟨t, ht⟩, (hintikkaSubstEval hHS A' t x ht hfree (Or.inl hsubst_in_S)).mp heval_subst⟩
        · -- False case: falseF (.ex x A') ∈ S → ¬ ∃ a, eval (assignUpdate s x a) A'
          intro hF ⟨⟨t, ht⟩, heval⟩
          have hfree : isFreeForN t x A' := hHS.h6 x A' t ht (Or.inr (Or.inr (Or.inr hF)))
          have hsubst_in_S := hHS.h3 (TypeC.fEx x A') hF t ht hfree
          have hdepth_sub : formulaDepth (formulaSubstN A' t x) ≤ n := by
            rw [formulaSubstN_depth]; simp [formulaDepth] at hle; omega
          have hneval := (ih_n (formulaSubstN A' t x) hdepth_sub).2 hsubst_in_S
          apply hneval
          exact (hintikkaSubstEval hHS A' t x ht hfree (Or.inr hsubst_in_S)).mpr heval
  intro sf hsf; cases sf with
  | trueF A => exact (key A).1 hsf
  | falseF A => exact (key A).2 hsf

/-- Lemma 5.4.5: Every Hintikka set S over its occurrence-language term
algebra H is satisfiable. There exists a structure M and assignment s such that every signed formula in S is satisfied. -/
@[blueprint "chap5__lemma_5_4_5" (main := true)]
theorem hintikka_set_satisfiable {L : Language} (hL : L.withoutEquality)
    (H : Set (Term L)) (S : Set (SignedFormula L))
    (hHS : IsHintikkaSet L hL H S) :
    ∃ (M : Structure L) (s : Assignment M),
      ∀ sf, sf ∈ S → SignedFormula.satisfiedBy M s sf 

end LCS.FirstOrder.Gentzen.Hintikka
end
