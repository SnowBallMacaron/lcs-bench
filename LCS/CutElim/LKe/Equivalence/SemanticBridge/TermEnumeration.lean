import LCS.Item
import LCS.Util
import LCS.CutElim.LKe
import LCS.CutElim.CompletenessBridge
import LCS.FirstOrder.Equality.Completeness
import LCS.FirstOrder.Semantics.Subformulae

section
namespace LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Equality.Completeness
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.CompletenessBridge
open LCS.FirstOrder.Equality

-- ===================================================================
-- Semantic bridge infrastructure: finite-support term enumeration
-- ===================================================================
/-- Diagonal successor on pairs of naturals. -/
def validBridgePairStep : Nat × Nat → Nat × Nat
  | (a, 0) => (0, a + 1)
  | (a, b + 1) => (a + 1, b)

/-- Diagonal enumeration of pairs of naturals. -/
def validBridgeUnpair : Nat → Nat × Nat
  | 0 => (0, 0)
  | n + 1 => validBridgePairStep (validBridgeUnpair n)

/-- A right inverse to `validBridgeUnpair`.  The recursion follows the
same diagonal traversal, but its well-founded measure avoids any use of
number-theoretic pairing infrastructure. -/
def validBridgePair : Nat → Nat → Nat
  | 0, 0 => 0
  | 0, b + 1 => validBridgePair b 0 + 1
  | a + 1, b => validBridgePair a (b + 1) + 1
termination_by a b => (a + b, a)
decreasing_by all_goals omega

theorem validBridgeUnpair_pair : ∀ a b,
    validBridgeUnpair (validBridgePair a b) = (a, b)
  | 0, 0 => by simp [validBridgePair, validBridgeUnpair]
  | 0, b + 1 => by
      rw [validBridgePair, validBridgeUnpair]
      simp [validBridgeUnpair_pair b 0, validBridgePairStep]
  | a + 1, b => by
      rw [validBridgePair, validBridgeUnpair]
      simp [validBridgeUnpair_pair a (b + 1), validBridgePairStep]
termination_by a b => (a + b, a)
decreasing_by all_goals omega

theorem validBridgePair_injective {a b c d : Nat}
    (h : validBridgePair a b = validBridgePair c d) :
    a = c ∧ b = d := by
  have hu := congrArg validBridgeUnpair h
  simpa [validBridgeUnpair_pair] using hu

mutual
  /-- Unranked raw terms used only to enumerate the terms of a finite
  support language. -/
  inductive ValidBridgeRawTerm : Type where
    | var : Nat → ValidBridgeRawTerm
    | const : Nat → ValidBridgeRawTerm
    | func : Nat → ValidBridgeRawTerms → ValidBridgeRawTerm

  /-- Strictly-positive lists for `ValidBridgeRawTerm`. -/
  inductive ValidBridgeRawTerms : Type where
    | nil : ValidBridgeRawTerms
    | cons : ValidBridgeRawTerm → ValidBridgeRawTerms → ValidBridgeRawTerms
end

mutual
  def validBridgeRawTermCode : ValidBridgeRawTerm → Nat
    | .var n => validBridgePair 0 n
    | .const n => validBridgePair 1 n
    | .func n ts =>
        validBridgePair 2 (validBridgePair n (validBridgeRawTermsCode ts))

  def validBridgeRawTermsCode : ValidBridgeRawTerms → Nat
    | .nil => 0
    | .cons t ts =>
        validBridgePair (validBridgeRawTermCode t)
          (validBridgeRawTermsCode ts) + 1
end

mutual
  theorem validBridgeRawTermCode_injective :
      Function.Injective validBridgeRawTermCode
    | .var a, .var b, h => by
        have hp := validBridgePair_injective h
        exact congrArg ValidBridgeRawTerm.var hp.2
    | .var a, .const b, h => by
        have hp := validBridgePair_injective h
        omega
    | .var a, .func b bs, h => by
        have hp := validBridgePair_injective h
        omega
    | .const a, .var b, h => by
        have hp := validBridgePair_injective h
        omega
    | .const a, .const b, h => by
        have hp := validBridgePair_injective h
        exact congrArg ValidBridgeRawTerm.const hp.2
    | .const a, .func b bs, h => by
        have hp := validBridgePair_injective h
        omega
    | .func a as, .var b, h => by
        have hp := validBridgePair_injective h
        omega
    | .func a as, .const b, h => by
        have hp := validBridgePair_injective h
        omega
    | .func a as, .func b bs, h => by
        have hp := validBridgePair_injective h
        have hp' := validBridgePair_injective hp.2
        have hab : a = b := hp'.1
        have has : as = bs :=
          validBridgeRawTermsCode_injective hp'.2
        cases hab
        cases has
        rfl

  theorem validBridgeRawTermsCode_injective :
      Function.Injective validBridgeRawTermsCode
    | .nil, .nil, _ => rfl
    | .nil, .cons b bs, h => by
        simp only [validBridgeRawTermsCode] at h
        omega
    | .cons a as, .nil, h => by
        simp only [validBridgeRawTermsCode] at h
        omega
    | .cons a as, .cons b bs, h => by
        simp only [validBridgeRawTermsCode] at h
        have hp0 :
            validBridgePair (validBridgeRawTermCode a)
                (validBridgeRawTermsCode as) =
              validBridgePair (validBridgeRawTermCode b)
                (validBridgeRawTermsCode bs) := by
          omega
        have hp := validBridgePair_injective hp0
        have hab : a = b := validBridgeRawTermCode_injective hp.1
        have has : as = bs := validBridgeRawTermsCode_injective hp.2
        cases hab
        cases has
        rfl
end

noncomputable def validBridgeRawEnumerate (n : Nat) :
    ValidBridgeRawTerm := by
  classical
  exact if h : ∃ t, validBridgeRawTermCode t = n then
      Classical.choose h
    else
      .var 0

theorem validBridgeRawEnumerate_surjective :
    Function.Surjective validBridgeRawEnumerate := by
  intro t
  refine ⟨validBridgeRawTermCode t, ?_⟩
  unfold validBridgeRawEnumerate
  split
  · rename_i h
    apply validBridgeRawTermCode_injective
    exact Classical.choose_spec h
  · rename_i h
    exact (h ⟨t, rfl⟩).elim

noncomputable instance validBridgeCountableRawTerm :
    Countable ValidBridgeRawTerm where
  enumerate := validBridgeRawEnumerate
  enumerate_surj := validBridgeRawEnumerate_surjective

def ValidBridgeRawTerms.ofList :
    List ValidBridgeRawTerm → ValidBridgeRawTerms
  | [] => .nil
  | t :: ts => .cons t (ValidBridgeRawTerms.ofList ts)

mutual
  /-- Interpret raw terms using two finite symbol lists.  Invalid raw
  symbol indices harmlessly decode as `x₀`; surjectivity only uses valid
  indices. -/
  def validBridgeRawToTerm {L : Language}
      (fs : List L.funSymbols) (cs : List L.constSymbols) :
      ValidBridgeRawTerm → Term L
    | .var n => .var n
    | .const n =>
        match cs[n]? with
        | some c => .const c
        | none => .var 0
    | .func n ts =>
        match fs[n]? with
        | some f =>
            .func f (fun i =>
              (validBridgeRawTermsToList fs cs ts)[i.val]?.getD (.var 0))
        | none => .var 0

  def validBridgeRawTermsToList {L : Language}
      (fs : List L.funSymbols) (cs : List L.constSymbols) :
      ValidBridgeRawTerms → List (Term L)
    | .nil => []
    | .cons t ts =>
        validBridgeRawToTerm fs cs t ::
          validBridgeRawTermsToList fs cs ts
end

theorem validBridgeRawTermsToList_ofList {L : Language}
    (fs : List L.funSymbols) (cs : List L.constSymbols)
    (ts : List ValidBridgeRawTerm) :
    validBridgeRawTermsToList fs cs (ValidBridgeRawTerms.ofList ts) =
      ts.map (validBridgeRawToTerm fs cs) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp [ValidBridgeRawTerms.ofList, validBridgeRawTermsToList, ih]

theorem validBridgeRawToTerm_surjective {L : Language}
    (fs : List L.funSymbols) (cs : List L.constSymbols)
    (hfs : ∀ f : L.funSymbols, f ∈ fs)
    (hcs : ∀ c : L.constSymbols, c ∈ cs) :
    Function.Surjective (validBridgeRawToTerm fs cs) := by
  intro t
  induction t with
  | var n =>
      exact ⟨.var n, rfl⟩
  | const c =>
      obtain ⟨n, hn⟩ := (List.mem_iff_getElem?).mp (hcs c)
      refine ⟨.const n, ?_⟩
      simp [validBridgeRawToTerm, hn]
  | func f ts ih =>
      obtain ⟨n, hn⟩ := (List.mem_iff_getElem?).mp (hfs f)
      let rawArgs : Fin (L.funArity f) → ValidBridgeRawTerm :=
        fun i => Classical.choose (ih i)
      let rawList : List ValidBridgeRawTerm := List.ofFn rawArgs
      refine ⟨.func n (ValidBridgeRawTerms.ofList rawList), ?_⟩
      simp only [validBridgeRawToTerm, hn, rawList,
        validBridgeRawTermsToList_ofList, List.map_ofFn]
      congr 1
      funext i
      have hspec :
          validBridgeRawToTerm fs cs (rawArgs i) = ts i :=
        Classical.choose_spec (ih i)
      have hget :
          (List.ofFn (fun j => validBridgeRawToTerm fs cs (rawArgs j)))[i.val]? =
            some (validBridgeRawToTerm fs cs (rawArgs i)) := by
        apply List.getElem?_eq_some_iff.mpr
        refine ⟨by simp, ?_⟩
        simp
      simp [hget, hspec]

@[reducible]
noncomputable def validBridgeTermCountable (L : Language)
    (fs : List L.funSymbols) (cs : List L.constSymbols)
    (hfs : ∀ f : L.funSymbols, f ∈ fs)
    (hcs : ∀ c : L.constSymbols, c ∈ cs) :
    Countable (Term L) :=
  Countable.ofSurjection (validBridgeRawToTerm fs cs)
    (validBridgeRawToTerm_surjective fs cs hfs hcs)

end LCS.CutElim.LKe.Equivalence
end
