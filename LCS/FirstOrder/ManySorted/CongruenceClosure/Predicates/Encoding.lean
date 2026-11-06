import LCS.Item
import LCS.Util
import LCS.FirstOrder.ManySorted
import LCS.FirstOrder.ManySorted.Semantics
import LCS.FirstOrder.ManySorted.Equality
import LCS.FirstOrder.ManySorted.CongruenceClosure
import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision
import Attach
import LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates.Encoding.ProofsStamp

section
namespace LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates
open LCS.FirstOrder.ManySorted
open LCS.FirstOrder.ManySorted.Semantics
open LCS.FirstOrder.ManySorted.Equality
open LCS.FirstOrder.ManySorted.CongruenceClosure
open LCS.FirstOrder.ManySorted.CongruenceClosure.Decision
open LCS.Propositional.Semantics

/-- Predicate symbols with nonempty argument strings become Boolean-valued functions. -/
@[blueprint "chap10__lemma_10_6_4"]
def MSPositivePredicates (L : MSLanguage) := {P : L.predSymbols // L.predArity P ≠ []}

/-- Propositional letters become constants of Boolean sort. -/
@[blueprint "chap10__lemma_10_6_4"]
def MSNullaryPredicates (L : MSLanguage) := {P : L.predSymbols // L.predArity P = []}

/-- The lifted ranks of the original functions and positive-arity predicates. -/
@[blueprint "chap10__lemma_10_6_4"]
def boolExtendedFunRank (L : MSLanguage) :
    (L.funSymbols ⊕ MSPositivePredicates L) →
      (List (Option L.SortType)) × Option L.SortType
  | Sum.inl f => ((L.funRank f).1.map some, some (L.funRank f).2)
  | Sum.inr P => ((L.predArity P.val).map some, none)

/-- The original constants at data sorts; at Boolean sort, top and all
nullary predicates, as distinct symbols. -/
@[blueprint "chap10__lemma_10_6_4"]
def boolExtendedConstSymbols (L : MSLanguage) : Option L.SortType → Type
  | some s => L.constSymbols s
  | none => Unit ⊕ MSNullaryPredicates L

/-- The Boolean extension used in Lemma 10.6.4. Positive predicates become
functions, nullary predicates become constants, and top is a separate constant.
Every function retains a nonempty argument string. -/
@[blueprint "chap10__lemma_10_6_4"]
def boolExtendedLanguage (L : MSLanguage) : MSLanguage where
  SortType := Option L.SortType
  someSort := none
  funSymbols := L.funSymbols ⊕ MSPositivePredicates L
  funRank := boolExtendedFunRank L
  funRank_nonempty := by
    intro f
    cases f with
    | inl f => exact fun h => L.funRank_nonempty f (List.map_eq_nil_iff.mp h)
    | inr P => exact fun h => P.property (List.map_eq_nil_iff.mp h)
  constSymbols := boolExtendedConstSymbols L
  predSymbols := Empty
  predArity := fun p => nomatch p
  hasEquality := true

-- ===================================================================
-- Lemma 10.6.4 (companion defs): the bool sort and ⊤
-- ===================================================================

/-- Lemma 10.6.4 (companion): the distinguished bool sort of `L'`,
`MSBoolSort L = (none : Option L.SortType)` — the new sort added to
`S(C)` so that `S(C)` also contains bool. Both "`⊤` as a constant of
sort bool" and "predicates as functions of output sort bool" target this
sort. -/
@[blueprint "chap10__lemma_10_6_4"]
def MSBoolSort (L : MSLanguage) :
    (boolExtendedLanguage L).SortType :=
  (none : Option L.SortType)

/-- Lemma 10.6.4 (required): the logical constant `⊤` of sort bool — the
`Sum.inl ()` constant of the bool sort `none` of `L'`, "the
logical constant always interpreted as T". Lives at `MSBoolSort L`. -/
@[blueprint "chap10__lemma_10_6_4"]
def msTopConst (L : MSLanguage) :
    MSTerm (boolExtendedLanguage L) (MSBoolSort L) :=
  MSTerm.const (L := boolExtendedLanguage L) (MSBoolSort L)
    (Sum.inl () : (boolExtendedLanguage L).constSymbols (MSBoolSort L))

/-- The Boolean term representing an atom: a positive-arity predicate is a
function application; a nullary predicate is its own Boolean constant. The
argument vector uses the lifted original arity in both cases. -/
@[blueprint "chap10__lemma_10_6_4"]
def msPredAsFuncTerm (L : MSLanguage) (P : L.predSymbols)
    (args : (i : Fin ((L.predArity P).map some).length) →
      MSTerm (boolExtendedLanguage L)
        (((L.predArity P).map some).get i)) :
    MSTerm (boolExtendedLanguage L) (MSBoolSort L) :=
  if h : (L.predArity P).length = 0 then
    MSTerm.const (L := boolExtendedLanguage L) (MSBoolSort L)
      (Sum.inr ⟨P, List.length_eq_zero_iff.mp h⟩)
  else
    MSTerm.func (L := boolExtendedLanguage L)
      (Sum.inr ⟨P, fun hn => h (by rw [hn]; rfl)⟩) args

-- ===================================================================
-- Lemma 10.6.4 (required defs): the atom-as-equation encoding
-- ===================================================================

/-- Lemma 10.6.4 (required): the bool-equation `(P t₁…t_k ≐_bool ⊤)` that
an atomic predicate formula is encoded as. This is the
atomic-predicate-as-equation encoding, and for a positive atom the
"positive atom replacement `P = ⊤`". Uses `MSFormula.eq_` at the bool
sort `MSBoolSort L`, with `rfl` discharging the `hasEquality = true`
proof obligation (`boolExtendedLanguage` sets `hasEquality := true`). -/
@[blueprint "chap10__lemma_10_6_4"]
def msEncodeAtom (L : MSLanguage) (P : L.predSymbols)
    (args : (i : Fin ((L.predArity P).map some).length) →
      MSTerm (boolExtendedLanguage L)
        (((L.predArity P).map some).get i)) :
    MSFormula (boolExtendedLanguage L) :=
  MSFormula.eq_ (L := boolExtendedLanguage L) rfl (MSBoolSort L)
    (msPredAsFuncTerm L P args) (msTopConst L)

/-- Lemma 10.6.4 (required): the encoding `¬(P t₁…t_k ≐_bool ⊤)` of a
negated atomic predicate formula `¬P t₁…t_k`. This is the "negative atom
replacement `¬(P = ⊤)`". -/
@[blueprint "chap10__lemma_10_6_4"]
def msEncodeNegAtom (L : MSLanguage) (P : L.predSymbols)
    (args : (i : Fin ((L.predArity P).map some).length) →
      MSTerm (boolExtendedLanguage L)
        (((L.predArity P).map some).get i)) :
    MSFormula (boolExtendedLanguage L) :=
  MSFormula.neg (msEncodeAtom L P args)

/-- Lemma 10.6.4 (required, helper): lift a term `t : MSTerm L s` over the
original language to the bool-extended language `L'` at sort `some s`,
relabelling every constant/variable/function symbol through the
`Option`/`Sum.inl` injections. This is the genuine term-level half of the
syntactic transformation `C ↦ C'` (it is NEVER the identity — it changes
the language). -/
@[blueprint "chap10__lemma_10_6_4"]
def msLiftTerm (L : MSLanguage) :
    {s : L.SortType} → MSTerm L s →
      MSTerm (boolExtendedLanguage L) (some s)
  | _, MSTerm.var s i => MSTerm.var (L := boolExtendedLanguage L) (some s) i
  | _, MSTerm.const s c =>
      MSTerm.const (L := boolExtendedLanguage L) (some s)
        (show (boolExtendedLanguage L).constSymbols (some s) from c)
  | _, MSTerm.func f ts =>
      -- `f` becomes `Sum.inl f`; its lifted rank is
      -- `((L.funRank f).1.map some, some (L.funRank f).2)`, so the output
      -- sort `some (L.funRank f).2` matches and each lifted argument lies
      -- at `some ((L.funRank f).1.get i)`. The recursive call is taken on
      -- the STRUCTURAL subterm `ts j` (`j : Fin (L.funRank f).1.length`),
      -- keeping the decrease visible to the termination checker; the index
      -- and sort of the bool-extended argument family are matched by `▸`.
      MSTerm.func (L := boolExtendedLanguage L) (Sum.inl f)
        (fun i =>
          let j : Fin (L.funRank f).1.length :=
            ⟨i.val, by
              have := i.isLt
              simpa [boolExtendedLanguage, boolExtendedFunRank, List.length_map]
                using this⟩
          have hsort :
              (((boolExtendedLanguage L).funRank (Sum.inl f)).1.get i) =
                some ((L.funRank f).1.get j) := by
            simp [boolExtendedLanguage, boolExtendedFunRank,
              List.get_eq_getElem, List.getElem_map, j]
            all_goals exact List.getElem_map some
          hsort ▸ msLiftTerm L (ts j))
  termination_by _ t => msTermSize t
  decreasing_by
    simp only [msTermSize]
    have hle := msTermSize_foldl_ofFn_ge_elem (L.funRank f).1.get ts ⟨i.val, by
      have := i.isLt
      simpa [boolExtendedLanguage, boolExtendedFunRank, List.length_map] using this⟩
    omega

/-- Lemma 10.6.4 (required): the genuine recursive encoder
`C ↦ C' = msEncodeConjunction L C`. Recursing structurally on the
conjunction-of-literals `C`:

* an equality literal `t ≐_s u` is relabelled to the bool-extended
  language at sort `some s` (`msLiftTerm` on both sides);
* a positive predicate atom `MSFormula.pred P ts` is replaced by
  `msEncodeAtom L P (lifted ts)` — the equation `(P t₁…t_k ≐_bool ⊤)`;
* a negated atom `MSFormula.neg (MSFormula.pred P ts)` by
  `msEncodeNegAtom`;
* a conjunction recurses on both conjuncts; negations and other
  connectives recurse structurally.

Yields `C'`, the conjunction of equations and negations of equations
obtained from `C`. This IS "conjunction `C'` of equations from literals"
(Pattern 3: a real syntactic transformation, never the identity). The
predicate-application arguments `ts i : MSTerm L ((L.predArity P).get i)`
are lifted to `some ((L.predArity P).get i)`, exactly the i-th argument
sort of `(boolExtendedLanguage L).funRank (Sum.inr P)`. -/
@[blueprint "chap10__lemma_10_6_4"]
def msEncodeConjunction (L : MSLanguage) :
    MSFormula L → MSFormula (boolExtendedLanguage L)
  | MSFormula.falsum => MSFormula.falsum
  | MSFormula.eq_ _ s t u =>
      MSFormula.eq_ (L := boolExtendedLanguage L) rfl (some s)
        (msLiftTerm L t) (msLiftTerm L u)
  | MSFormula.pred P ts =>
      msEncodeAtom L P (fun i => by
        have hi : i.val < (L.predArity P).length := by
          have := i.isLt
          simpa [boolExtendedLanguage, boolExtendedFunRank, List.length_map]
            using this
        have hsort :
            (((L.predArity P).map some).get i) =
              some ((L.predArity P).get ⟨i.val, hi⟩) := by
          simp [boolExtendedLanguage, boolExtendedFunRank, List.get_eq_getElem, List.getElem_map]
          all_goals exact List.getElem_map some
        exact hsort ▸ msLiftTerm L (ts ⟨i.val, hi⟩))
  | MSFormula.neg (MSFormula.pred P ts) =>
      msEncodeNegAtom L P (fun i => by
        have hi : i.val < (L.predArity P).length := by
          have := i.isLt
          simpa [boolExtendedLanguage, boolExtendedFunRank, List.length_map]
            using this
        have hsort :
            (((L.predArity P).map some).get i) =
              some ((L.predArity P).get ⟨i.val, hi⟩) := by
          simp [boolExtendedLanguage, boolExtendedFunRank, List.get_eq_getElem, List.getElem_map]
          all_goals exact List.getElem_map some
        exact hsort ▸ msLiftTerm L (ts ⟨i.val, hi⟩))
  | MSFormula.neg A => MSFormula.neg (msEncodeConjunction L A)
  | MSFormula.conj A B =>
      MSFormula.conj (msEncodeConjunction L A) (msEncodeConjunction L B)
  | MSFormula.disj A B =>
      MSFormula.disj (msEncodeConjunction L A) (msEncodeConjunction L B)
  | MSFormula.impl A B =>
      MSFormula.impl (msEncodeConjunction L A) (msEncodeConjunction L B)
  | MSFormula.equiv_ A B =>
      MSFormula.equiv_ (msEncodeConjunction L A) (msEncodeConjunction L B)
  | MSFormula.all s i A => MSFormula.all (some s) i (msEncodeConjunction L A)
  | MSFormula.ex s i A => MSFormula.ex (some s) i (msEncodeConjunction L A)

-- ===================================================================
-- Lemma 10.6.4 (required theorems): R is a G(C')-congruence; the two
-- collision cases (non-bool sort, atom = ⊤)
-- ===================================================================

/-- Lemma 10.6.4 (helper): the carrier family of the encoded `L'`-structure
built from a model `M` of `L`: a non-bool sort `some s` keeps `M`'s carrier
`M_s`, the bool sort `none` is interpreted as `BoolVal` (the textbook's
BOOL). -/
@[blueprint "chap10__lemma_10_6_4"]
def encodeCarrier (L : MSLanguage) (M : MSStructure L) :
    (boolExtendedLanguage L).SortType → Type
  | some s => M.carrier s
  | none   => BoolVal

/-- Lemma 10.6.4 (helper): recast a single bool-extended argument of the lifted
function symbol `Sum.inl f` back to an `M`-argument. The `i`-th argument of
`Sum.inl f` lies in `encodeCarrier L M ((L.funRank f).1.map some).get ⟨i,_⟩`,
which (after `List.length_map`/`List.getElem_map`) is `M.carrier ((L.funRank
f).1.get j)`. Packaged as its own `def` so the `interpFunc` clause and the
computation lemma `encodeModel_interpFunc_inl_eq` reference a single named
recast (and the cast is a single `▸` on the value). -/
@[blueprint "chap10__lemma_10_6_4"]
noncomputable def inlArgRecast (L : MSLanguage)
    (M : MSStructure L) (f : L.funSymbols)
    (args : (i : Fin (((boolExtendedLanguage L).funRank (Sum.inl f)).1).length) →
      encodeCarrier L M (((boolExtendedLanguage L).funRank (Sum.inl f)).1.get i))
    (j : Fin (L.funRank f).1.length) : M.carrier ((L.funRank f).1.get j) :=
  have hi : j.val < (((boolExtendedLanguage L).funRank (Sum.inl f)).1).length := by
    have := j.isLt
    simpa [boolExtendedLanguage, boolExtendedFunRank, List.length_map] using this
  have hsort :
      (((boolExtendedLanguage L).funRank (Sum.inl f)).1.get ⟨j.val, hi⟩) =
        some ((L.funRank f).1.get j) := by
    simp [boolExtendedLanguage, boolExtendedFunRank, List.get_eq_getElem, List.getElem_map]
  (show encodeCarrier L M (some ((L.funRank f).1.get j))
    = M.carrier ((L.funRank f).1.get j) from rfl) ▸ (hsort ▸ args ⟨j.val, hi⟩)

/-- Lemma 10.6.4 (helper): the encoded `L'`-structure built from a model `M`
of `L`. Non-bool sorts `some s` use `M`'s carriers `M_s`; the bool sort `none`
is `BoolVal`. An original function symbol `Sum.inl f` is interpreted by
`f_M` (its lifted-rank argument family is re-indexed back to `M`'s argument
family by the `List.length_map`/`List.getElem_map` equalities); a
positive predicate-as-function symbol `Sum.inr P` is interpreted by `P_M` (the
`BoolVal` value of `P` in `M`). Constants of sort `some s` are `M`'s constants
`c_M`; the Boolean constant `⊤` is `T`, and each nullary predicate
constant is interpreted by its original predicate value. There are no
predicate symbols (`L'.predSymbols = Empty`). -/
@[blueprint "chap10__lemma_10_6_4"]
noncomputable def encodeModel (L : MSLanguage)
    (M : MSStructure L) : MSStructure (boolExtendedLanguage L) where
  carrier := encodeCarrier L M
  carrierNonempty := fun s => by
    cases s with
    | none => exact ⟨BoolVal.T⟩
    | some s => exact M.carrierNonempty s
  interpFunc := fun g args =>
    match g with
    | Sum.inl f =>
      -- `Sum.inl f` keeps rank `((L.funRank f).1.map some, some (L.funRank f).2)`;
      -- the output carrier is `M.carrier (L.funRank f).2`, and each argument
      -- lies in `M.carrier ((L.funRank f).1.get j)` after the `map some` recast
      -- (packaged in `inlArgRecast`, giving the clean computation lemma below).
      show M.carrier (L.funRank f).2 from M.interpFunc f (inlArgRecast L M f args)
    | Sum.inr P =>
      -- `Sum.inr P` has rank `((L.predArity P.val).map some, none)`; the output
      -- carrier is `BoolVal`, and the arguments recast to `M`'s predicate
      -- argument family, fed to `P_M`.
      show BoolVal from M.interpPred P.val (fun j =>
        have hi : j.val < (((L.predArity P.val).map some)).length := by
          have := j.isLt
          simpa [boolExtendedLanguage, boolExtendedFunRank, List.length_map] using this
        have hsort :
            (((L.predArity P.val).map some).get ⟨j.val, hi⟩) =
              some ((L.predArity P.val).get j) := by
          simp [boolExtendedLanguage, boolExtendedFunRank,
            List.get_eq_getElem, List.getElem_map]
        (show encodeCarrier L M (some ((L.predArity P.val).get j))
          = M.carrier ((L.predArity P.val).get j) from rfl) ▸ (hsort ▸ args ⟨j.val, hi⟩))
  interpConst := fun s c => by
    cases s with
    | none =>
      cases c with
      | inl _ => exact (BoolVal.T : encodeCarrier L M none)
      | inr P =>
        exact M.interpPred P.val (fun i => by
          have hi := i.isLt
          simp only [P.property, List.length_nil] at hi
          exact False.elim (Nat.not_lt_zero _ hi))
    | some s => exact (M.interpConst s c : encodeCarrier L M (some s))
  interpPred := fun p _ => nomatch p

/-- Lemma 10.6.4 (helper): the lifted assignment over `L'` induced by an
assignment `v` of `M`: a variable of a non-bool sort `some s` keeps `v`'s
value `v s i`, a bool-sorted variable maps to the junk `T`. -/
@[blueprint "chap10__lemma_10_6_4"]
def encodeAssignment (L : MSLanguage) {M : MSStructure L}
    (v : MSAssignment M) : MSAssignment (encodeModel L M) :=
  fun s => by
    cases s with
    | none => exact fun _ => (BoolVal.T : encodeCarrier L M none)
    | some s => exact fun i => (v s i : encodeCarrier L M (some s))

/-- Lemma 10.6.4 (helper, computation): `encodeModel`'s interpretation of the
lifted function symbol `Sum.inl f` is `M.interpFunc f` applied to the recast
argument family `inlArgRecast`. Holds by `rfl` (it is the `Sum.inl` clause of
`encodeModel.interpFunc`), and lets the func case of
`msTermEval_encodeModel_liftTerm` `rw` away the structure interpretation. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem encodeModel_interpFunc_inl_eq (L : MSLanguage)
    (M : MSStructure L) (f : L.funSymbols)
    (args : (i : Fin (((boolExtendedLanguage L).funRank (Sum.inl f)).1).length) →
      (encodeModel L M).carrier (((boolExtendedLanguage L).funRank (Sum.inl f)).1.get i)) :
    (encodeModel L M).interpFunc (Sum.inl f) args =
      M.interpFunc f (inlArgRecast L M f args) 

/-- Lemma 10.6.4 (helper): the recast argument `inlArgRecast L M f args j` is
heterogeneously equal to the underlying bool-extended argument `args ⟨j.val,
hi⟩` — the two carrier casts in `inlArgRecast` are HEq-identity and the index
proof is irrelevant. Used to peel `inlArgRecast` off in the func case. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem inlArgRecast_heq (L : MSLanguage) (M : MSStructure L)
    (f : L.funSymbols)
    (args : (i : Fin (((boolExtendedLanguage L).funRank (Sum.inl f)).1).length) →
      encodeCarrier L M (((boolExtendedLanguage L).funRank (Sum.inl f)).1.get i))
    (j : Fin (L.funRank f).1.length)
    (hi : j.val < (((boolExtendedLanguage L).funRank (Sum.inl f)).1).length) :
    inlArgRecast L M f args j ≍ args ⟨j.val, hi⟩ 

/-- Lemma 10.6.4 (helper): the bool-extended meaning of a sort-cast lift
`h ▸ msLiftTerm L t` (for `h : b = some s2`) is heterogeneously equal to the
`M`-meaning of `t`, given the term-transfer fact `ht` for `t`. The sort-cast
is HEq-identity, then the term-transfer fact rewrites the meaning and the
remaining (rfl) carrier-cast is identity. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem lift_meaning_heq (L : MSLanguage)
    (M : MSStructure L) (v : MSAssignment M)
    {s2 : L.SortType} (t : MSTerm L s2)
    {b : (boolExtendedLanguage L).SortType} (h : b = some s2)
    (ht : msTermEval (encodeModel L M) (encodeAssignment L v) (msLiftTerm L t) =
            (show M.carrier s2 = encodeCarrier L M (some s2) from rfl) ▸
              msTermEval M v t) :
    msTermEval (encodeModel L M) (encodeAssignment L v) (h ▸ msLiftTerm L t) ≍
      msTermEval M v t 

/-- Lemma 10.6.4 (helper): the term-meaning transfer of the lift `msLiftTerm`:
the meaning of `msLiftTerm L t` (a sort-`some s` term over `L'`) in the encoded
model `encodeModel L M` under `encodeAssignment L v` equals the meaning of `t`
in `M` under `v` (identifying `encodeCarrier L M (some s)` with `M_s`). The
backbone of the model transfer; proved by induction on `t`. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem msTermEval_encodeModel_liftTerm (L : MSLanguage)
    (M : MSStructure L) (v : MSAssignment M) :
    ∀ {s : L.SortType} (t : MSTerm L s),
      msTermEval (encodeModel L M) (encodeAssignment L v) (msLiftTerm L t) =
        (show M.carrier s = encodeCarrier L M (some s) from rfl) ▸
          msTermEval M v t 

-- ===================================================================
-- Lemma 10.6.4 (model transfer): the FORMULA-level transfer lemma
-- `msFormulaEval (encodeModel) (msEncodeConjunction C) (encodeAssignment v)
--   = msFormulaEval M C v`, by induction on `C`.
-- ===================================================================

/-- Lemma 10.6.4 (helper): a `BoolVal` is determined by whether it is `T`, so
two `BoolVal`s with the same "`= T`" status are equal. Lets the atomic transfer
cases be argued through the `= T` iff of `msFormulaEval_eq_T_iff`. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem boolVal_eq_of_T_iff {x y : BoolVal} (h : x = BoolVal.T ↔ y = BoolVal.T) :
    x = y 

/-- Lemma 10.6.4 (helper): two lifted terms have equal meaning in the encoded
model under the lifted assignment iff the originals have equal meaning in `M`.
Both meanings are `rfl`-cast images of the `M`-meanings
(`msTermEval_encodeModel_liftTerm`), so the equalities coincide. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem liftTerm_eq_iff (L : MSLanguage) (M : MSStructure L)
    (v : MSAssignment M) {s : L.SortType} (t u : MSTerm L s) :
    (msTermEval (encodeModel L M) (encodeAssignment L v) (msLiftTerm L t) =
      msTermEval (encodeModel L M) (encodeAssignment L v) (msLiftTerm L u))
      ↔ (msTermEval M v t = msTermEval M v u) 

/-- Lemma 10.6.4 (helper): a positive predicate atom `pred P ts` of `C` and its
bool-equation encoding `msEncodeAtom L P (lifted ts)` evaluate to the SAME
`BoolVal` (in the encoded model under the lifted assignment, vs `M` under `v`).
The encoded atom is `(P t₁…t_k ≐_bool ⊤)`; it is `T` iff the predicate term's
meaning equals `⊤`'s (`= T`), and that meaning is `M.interpPred P (…)` =
`msFormulaEval M (pred P ts) v`. -/
@[attach_debt, blueprint "chap10__lemma_10_6_4"]
theorem msEncodeAtom_eval (L : MSLanguage) (M : MSStructure L)
    (v : MSAssignment M) (P : L.predSymbols)
    (ts : (i : Fin (L.predArity P).length) → MSTerm L ((L.predArity P).get i)) :
    msFormulaEval (encodeModel L M)
        (msEncodeAtom L P (fun i => by
          have hi : i.val < (L.predArity P).length := by
            have := i.isLt
            simpa [boolExtendedLanguage, boolExtendedFunRank, List.length_map] using this
          have hsort :
              (((L.predArity P).map some).get i) =
                some ((L.predArity P).get ⟨i.val, hi⟩) := by
            simp only [boolExtendedLanguage, boolExtendedFunRank, List.get_eq_getElem]
            all_goals exact List.getElem_map some
          exact hsort ▸ msLiftTerm L (ts ⟨i.val, hi⟩)))
        (encodeAssignment L v)
      = msFormulaEval M (MSFormula.pred P ts) v 

/-- Lemma 10.6.4 (helper): updating the lifted assignment at the lifted variable
`(some s, i)` with `a : M_s` equals lifting the updated assignment `v[x_i := a]`.
The `none`/non-matching-sort branches agree, and the matching branch agrees up
to the proof-irrelevant `▸` cast on `a`. The quantifier correspondence that
lets `forallM`/`existsM` transfer through the encoding. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem encodeAssignment_update (L : MSLanguage)
    (M : MSStructure L) (v : MSAssignment M) (s : L.SortType) (i : Nat) (a : M.carrier s) :
    msAssignUpdate (encodeModel L M) (encodeAssignment L v) (some s) i
        (show (encodeModel L M).carrier (some s) from a)
      = encodeAssignment L (msAssignUpdate M v s i a) 

/-- Lemma 10.6.4 (helper): negation evaluates to `hNeg` of the operand meaning
(`msFormulaEval` `neg` clause); holds by `rfl`. Named so the negation cases of
the formula-transfer induction can `rw` on both sides without unfolding the
operand. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem msFormulaEval_neg' {L' : MSLanguage} (M : MSStructure L') (A : MSFormula L')
    (v : MSAssignment M) :
    msFormulaEval M (MSFormula.neg A) v = hNeg (msFormulaEval M A v) 

/-- Lemma 10.6.4 (model transfer, core): the FORMULA-level transfer — the
encoded conjunction `C' = msEncodeConjunction L C` evaluated in the encoded
model `encodeModel L M` under the lifted assignment `encodeAssignment L v`
gives the SAME `BoolVal` as `C` evaluated in `M` under `v`. By induction on `C`:
equalities use `liftTerm_eq_iff`; positive/negative predicate atoms use
`msEncodeAtom_eval` (`P ≐_bool ⊤` is interpreted as the predicate value);
connectives recurse via the IH; quantifiers transfer via the
update-correspondence `encodeAssignment_update`. -/
@[blueprint "chap10__lemma_10_6_4"]
theorem msFormulaEval_encodeModel_encode (L : MSLanguage)
    (M : MSStructure L) :
    ∀ (C : MSFormula L) (v : MSAssignment M),
      msFormulaEval (encodeModel L M) (msEncodeConjunction L C) (encodeAssignment L v)
        = msFormulaEval M C v 

@[blueprint "chap10__lemma_10_6_4"]
theorem encodePreservesSat (L : MSLanguage) (C : MSFormula L)
    (h : Decision.msSatisfiable C) :
    Decision.msSatisfiable (msEncodeConjunction L C) 

end LCS.FirstOrder.ManySorted.CongruenceClosure.Predicates
end

