import LCS.Item
import LCS.Util
import LCS.CutElim.Interpolation
import LCS.CutElim.LKe
import LCS.FirstOrder.Equality.Completeness
import LCS.CutElim.Interpolation.Equality.Axioms
import LCS.CutElim.Interpolation.Equality.Support
import Attach
import LCS.CutElim.Interpolation.Equality.Replay.ProofsStamp

section
namespace LCS.CutElim.Interpolation.Equality
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.CutElim.Interpolation
open LCS.FirstOrder.Completeness
open LCS.FirstOrder.Equality
open LCS.FirstOrder.Equality.Completeness
open LCS.FirstOrder.Gentzen.Hintikka

-- ATTACH-BLOCKER: private declaration
private def captureSafeTermMap {L : Language}
    (A : FormulaN L) (vars : List Nat) (us : List (Term L))
    (x : Nat) : Term L :=
  let fresh := captureSafeFreshVars A vars us
  termSubstTermsList
    (termSubstTermsList (.var x) vars (fresh.map (@Term.var L)))
    fresh us

-- ATTACH-BLOCKER: private declaration
private theorem captureSafeAllListInstance_eq_map {L : Language}
    (A : FormulaN L) (vars : List Nat) (us : List (Term L))
    (hOpen : formulaBVN A = ∅) :
    captureSafeAllListInstance A vars us =
      formulaMapVars (captureSafeTermMap A vars us) A := by
  exact formulaSubstTerms_twoStage A vars
    (captureSafeFreshVars A vars us) us hOpen

-- ATTACH-BLOCKER: private declaration
private def congruenceVars (n : Nat) : List Nat :=
  List.range n ++ (List.range n).map (fun i => n + i)

-- ATTACH-BLOCKER: private declaration
private def congruenceTerms {L : Language} {n : Nat}
    (ss ts : Fin n → Term L) : List (Term L) :=
  List.ofFn ss ++ List.ofFn ts

-- ATTACH-BLOCKER: private declaration
private theorem congruenceVars_length (n : Nat) :
    (congruenceVars n).length = 2 * n := by
  simp [congruenceVars]
  omega

-- ATTACH-BLOCKER: private declaration
private theorem congruenceTerms_length {L : Language} {n : Nat}
    (ss ts : Fin n → Term L) :
    (congruenceTerms ss ts).length = 2 * n := by
  simp [congruenceTerms]
  omega

-- ATTACH-BLOCKER: private declaration
private theorem congruenceVars_nodup (n : Nat) :
    (congruenceVars n).Nodup := by
  rw [congruenceVars, List.nodup_append]
  refine ⟨List.nodup_range, ?_, ?_⟩
  · exact List.Pairwise.map
      (fun i => n + i)
      (by
        intro i j hij hEq
        exact hij (Nat.add_left_cancel hEq))
      List.nodup_range
  · intro x hxRange y hyMap hEq
    rw [List.mem_map] at hyMap
    obtain ⟨i, hi, rfl⟩ := hyMap
    have hsmall := List.mem_range.mp hxRange
    omega

-- ATTACH-BLOCKER: private declaration
private theorem congruenceVars_get_y (n : Nat) (i : Fin n) :
    (congruenceVars n)[n + i.val]'(by
      rw [congruenceVars_length]
      omega) = n + i.val := by
  simp [congruenceVars, i.isLt]

-- ATTACH-BLOCKER: private declaration
private theorem congruenceVars_get_x (n : Nat) (i : Fin n) :
    (congruenceVars n)[i.val]'(by
      rw [congruenceVars_length]
      omega) = i.val := by
  simp [congruenceVars, i.isLt]

-- ATTACH-BLOCKER: private declaration
private theorem congruenceTerms_get_y {L : Language} {n : Nat}
    (ss ts : Fin n → Term L) (i : Fin n) :
    (congruenceTerms ss ts)[n + i.val]'(by
      rw [congruenceTerms_length]
      omega) = ts i := by
  simp [congruenceTerms, i.isLt]

-- ATTACH-BLOCKER: private declaration
private theorem congruenceTerms_get_x {L : Language} {n : Nat}
    (ss ts : Fin n → Term L) (i : Fin n) :
    (congruenceTerms ss ts)[i.val]'(by
      rw [congruenceTerms_length]
      omega) = ss i := by
  simp [congruenceTerms, i.isLt]

-- ATTACH-BLOCKER: private declaration
private theorem captureSafeCongruence_y {L : Language}
    (A : FormulaN L) {n : Nat} (ss ts : Fin n → Term L)
    (i : Fin n) :
    captureSafeTermMap A (congruenceVars n)
        (congruenceTerms ss ts) (n + i.val) =
      ts i := by
  have h := captureSafeSubst_var_at
    A (congruenceVars n) (congruenceTerms ss ts)
    (by rw [congruenceVars_length, congruenceTerms_length])
    (congruenceVars_nodup n)
    (n + i.val) (by rw [congruenceVars_length]; omega)
  simpa [captureSafeTermMap, congruenceVars_get_y,
    congruenceTerms_get_y] using h

-- ATTACH-BLOCKER: private declaration
private theorem captureSafeCongruence_x {L : Language}
    (A : FormulaN L) {n : Nat} (ss ts : Fin n → Term L)
    (i : Fin n) :
    captureSafeTermMap A (congruenceVars n)
        (congruenceTerms ss ts) i.val =
      ss i := by
  have h := captureSafeSubst_var_at
    A (congruenceVars n) (congruenceTerms ss ts)
    (by rw [congruenceVars_length, congruenceTerms_length])
    (congruenceVars_nodup n)
    i.val (by rw [congruenceVars_length]; omega)
  simpa [captureSafeTermMap, congruenceVars_get_x,
    congruenceTerms_get_x] using h

-- ATTACH-BLOCKER: private declaration
private def implicationBody {L : Language}
    (premises : List (FormulaN L)) (C : FormulaN L) : FormulaN L :=
  match premises with
  | [] => C
  | hd :: tl => FormulaN.impl (conjoinFormulae hd (hd :: tl)) C

-- ATTACH-BLOCKER: private declaration
private theorem formulaMapVars_conjoin {L : Language}
    (σ : Nat → Term L) (hd : FormulaN L) (tl : List (FormulaN L)) :
    formulaMapVars σ (conjoinFormulae hd (hd :: tl)) =
      conjoinFormulae (formulaMapVars σ hd)
        (formulaMapVars σ hd :: tl.map (formulaMapVars σ)) := by
  induction tl generalizing hd with
  | nil => rfl
  | cons A tl ih =>
    simp only [List.map_cons, conjoin_cons_cons, formulaMapVars]
    rw [ih]

-- ATTACH-BLOCKER: private declaration
private theorem formulaMapVars_implicationBody {L : Language}
    (σ : Nat → Term L) (premises : List (FormulaN L))
    (C : FormulaN L) :
    formulaMapVars σ (implicationBody premises C) =
      implicationBody (premises.map (formulaMapVars σ))
        (formulaMapVars σ C) := by
  cases premises with
  | nil => rfl
  | cons hd tl =>
      simp only [implicationBody, List.map_cons, formulaMapVars]
      rw [formulaMapVars_conjoin]

-- ATTACH-BLOCKER: private declaration
private theorem conjoin_bv_empty {L : Language}
    (hd : FormulaN L) (tl : List (FormulaN L))
    (hhd : formulaBVN hd = ∅)
    (htl : ∀ A ∈ tl, formulaBVN A = ∅) :
    formulaBVN (conjoinFormulae hd (hd :: tl)) = ∅ := by
  induction tl generalizing hd with
  | nil => exact hhd
  | cons A tl ih =>
    rw [conjoin_cons_cons]
    simp only [formulaBVN, hhd,
      ih A (htl A (List.mem_cons_self)) (fun B hB => htl B (List.mem_cons_of_mem A hB))]
    ext v
    simp [Set.union, Set.empty]

-- ATTACH-BLOCKER: private declaration
private theorem implicationBody_bv_empty {L : Language}
    (premises : List (FormulaN L)) (C : FormulaN L)
    (hPremises : ∀ A ∈ premises, formulaBVN A = ∅)
    (hC : formulaBVN C = ∅) :
    formulaBVN (implicationBody premises C) = ∅ := by
  cases premises with
  | nil => exact hC
  | cons hd tl =>
      simp only [implicationBody, formulaBVN]
      rw [conjoin_bv_empty hd tl
        (hPremises hd (List.mem_cons_self))
        (fun A hA => hPremises A (List.mem_cons_of_mem hd hA)),
        hC]
      ext v
      constructor
      · rintro (h | h) <;> exact h.elim
      · intro h
        exact h.elim

-- ATTACH-BLOCKER: private declaration
private def schematicEqPairs {L : Language}
    (hL : L.hasEquality = true) (n : Nat) : List (FormulaN L) :=
  (List.finRange n).map (fun i =>
    FormulaN.eq_ hL (.var i.val) (.var (n + i.val)))

-- ATTACH-BLOCKER: private declaration
private def concreteEqPairs {L : Language}
    (hL : L.hasEquality = true) {n : Nat}
    (ss ts : Fin n → Term L) : List (FormulaN L) :=
  (List.finRange n).map (fun i => FormulaN.eq_ hL (ss i) (ts i))

-- ATTACH-BLOCKER: private declaration
private def schematicFunCongBody {L : Language}
    (hL : L.hasEquality = true) (f : L.funSymbols) : FormulaN L :=
  let n := L.funArity f
  implicationBody (schematicEqPairs hL n)
    (FormulaN.eq_ hL
      (Term.func f (fun i => .var i.val))
      (Term.func f (fun i => .var (n + i.val))))

-- ATTACH-BLOCKER: private declaration
private def concreteFunCongBody {L : Language}
    (hL : L.hasEquality = true) (f : L.funSymbols)
    (ss ts : Fin (L.funArity f) → Term L) : FormulaN L :=
  implicationBody (concreteEqPairs hL ss ts)
    (FormulaN.eq_ hL (Term.func f ss) (Term.func f ts))

-- ATTACH-BLOCKER: private declaration
private theorem schematicFunCongBody_bv_empty {L : Language}
    (hL : L.hasEquality = true) (f : L.funSymbols) :
    formulaBVN (schematicFunCongBody hL f) = ∅ := by
  apply implicationBody_bv_empty
  · intro A hA
    rw [schematicEqPairs, List.mem_map] at hA
    obtain ⟨i, _, rfl⟩ := hA
    rfl
  · rfl

-- ATTACH-BLOCKER: private declaration
private theorem captureSafeFunCongBody {L : Language}
    (hL : L.hasEquality = true) (f : L.funSymbols)
    (ss ts : Fin (L.funArity f) → Term L) :
    captureSafeAllListInstance
        (schematicFunCongBody hL f)
        (congruenceVars (L.funArity f))
        (congruenceTerms ss ts) =
      concreteFunCongBody hL f ss ts := by
  rw [captureSafeAllListInstance_eq_map _ _ _
    (schematicFunCongBody_bv_empty hL f)]
  rw [schematicFunCongBody, formulaMapVars_implicationBody]
  unfold concreteFunCongBody
  congr 1
  · simp only [schematicEqPairs, concreteEqPairs, List.map_map]
    apply List.map_congr_left
    intro i hi
    simp only [Function.comp_apply, formulaMapVars, termMapVars]
    rw [captureSafeCongruence_x, captureSafeCongruence_y]
  · simp only [formulaMapVars, termMapVars]
    congr 2 <;> funext i
    · exact captureSafeCongruence_x _ ss ts i
    · exact captureSafeCongruence_y _ ss ts i

-- ATTACH-BLOCKER: private declaration
private theorem closedFunCongAxiom_eq_allList {L : Language}
    (hL : L.hasEquality = true) (f : L.funSymbols) :
    closedFunCongAxiom hL f =
      FormulaN.allList (congruenceVars (L.funArity f))
        (schematicFunCongBody hL f) := by
  unfold closedFunCongAxiom schematicFunCongBody schematicEqPairs
    implicationBody congruenceVars
  generalize hPairs :
      List.map
        (fun i : Fin (L.funArity f) =>
          FormulaN.eq_ hL (.var i.val)
            (.var (L.funArity f + i.val)))
        (List.finRange (L.funArity f)) = pairs
  cases pairs <;>
    simp [FormulaN.allList, List.foldr_append, List.foldr_map,
      hPairs]

-- ATTACH-BLOCKER: private declaration
private theorem folkProvable_closedFunCongBody {L : Language}
    (hL : L.hasEquality = true) (f : L.funSymbols)
    (ss ts : Fin (L.funArity f) → Term L) :
    folkProvable
      (Sequent.mk [closedFunCongAxiom hL f]
        [concreteFunCongBody hL f ss ts]) := by
  rw [closedFunCongAxiom_eq_allList]
  rw [← captureSafeFunCongBody]
  exact folkProvable_captureSafeAllListInstantiation
    (schematicFunCongBody hL f)
    (congruenceVars (L.funArity f))
    (congruenceTerms ss ts)
    (by rw [congruenceVars_length, congruenceTerms_length])
    (congruenceVars_nodup _)
    (schematicFunCongBody_bv_empty hL f)

-- ATTACH-BLOCKER: private declaration
private def schematicPredCongPremises {L : Language}
    (hL : L.hasEquality = true) (P : L.predSymbols) :
    List (FormulaN L) :=
  schematicEqPairs hL (L.predArity P) ++
    [FormulaN.predN P (fun i => .var i.val)]

-- ATTACH-BLOCKER: private declaration
private def concretePredCongPremises {L : Language}
    (hL : L.hasEquality = true) (P : L.predSymbols)
    (ss ts : Fin (L.predArity P) → Term L) :
    List (FormulaN L) :=
  concreteEqPairs hL ss ts ++ [FormulaN.predN P ss]

-- ATTACH-BLOCKER: private declaration
private def schematicPredCongBody {L : Language}
    (hL : L.hasEquality = true) (P : L.predSymbols) : FormulaN L :=
  let n := L.predArity P
  implicationBody (schematicPredCongPremises hL P)
    (FormulaN.predN P (fun i => .var (n + i.val)))

-- ATTACH-BLOCKER: private declaration
private def concretePredCongBody {L : Language}
    (hL : L.hasEquality = true) (P : L.predSymbols)
    (ss ts : Fin (L.predArity P) → Term L) : FormulaN L :=
  implicationBody (concretePredCongPremises hL P ss ts)
    (FormulaN.predN P ts)

-- ATTACH-BLOCKER: private declaration
private theorem schematicPredCongBody_bv_empty {L : Language}
    (hL : L.hasEquality = true) (P : L.predSymbols) :
    formulaBVN (schematicPredCongBody hL P) = ∅ := by
  apply implicationBody_bv_empty
  · intro A hA
    rcases List.mem_append.mp hA with hEq | hPred
    · rw [schematicEqPairs, List.mem_map] at hEq
      obtain ⟨i, _, rfl⟩ := hEq
      rfl
    · simp only [List.mem_singleton] at hPred
      subst A
      rfl
  · rfl

-- ATTACH-BLOCKER: private declaration
private theorem captureSafePredCongBody {L : Language}
    (hL : L.hasEquality = true) (P : L.predSymbols)
    (ss ts : Fin (L.predArity P) → Term L) :
    captureSafeAllListInstance
        (schematicPredCongBody hL P)
        (congruenceVars (L.predArity P))
        (congruenceTerms ss ts) =
      concretePredCongBody hL P ss ts := by
  rw [captureSafeAllListInstance_eq_map _ _ _
    (schematicPredCongBody_bv_empty hL P)]
  rw [schematicPredCongBody, formulaMapVars_implicationBody]
  unfold concretePredCongBody
  congr 1
  · unfold schematicPredCongPremises concretePredCongPremises
    rw [List.map_append]
    congr 1
    · simp only [schematicEqPairs, concreteEqPairs, List.map_map]
      apply List.map_congr_left
      intro i hi
      simp only [Function.comp_apply, formulaMapVars, termMapVars]
      rw [captureSafeCongruence_x, captureSafeCongruence_y]
    · simp only [List.map_singleton, formulaMapVars]
      congr 2
      funext i
      exact captureSafeCongruence_x _ ss ts i
  · simp only [formulaMapVars]
    congr 1
    funext i
    exact captureSafeCongruence_y _ ss ts i

-- ATTACH-BLOCKER: private declaration
private theorem closedPredCongAxiom_eq_allList {L : Language}
    (hL : L.hasEquality = true) (P : L.predSymbols) :
    closedPredCongAxiom hL P =
      FormulaN.allList (congruenceVars (L.predArity P))
        (schematicPredCongBody hL P) := by
  unfold closedPredCongAxiom schematicPredCongBody
    schematicPredCongPremises schematicEqPairs implicationBody
    congruenceVars
  generalize hPremises :
      List.map
          (fun i : Fin (L.predArity P) =>
            FormulaN.eq_ hL (.var i.val)
              (.var (L.predArity P + i.val)))
          (List.finRange (L.predArity P)) ++
        [FormulaN.predN P (fun i => .var i.val)] = premises
  cases premises <;>
    simp [FormulaN.allList, List.foldr_append, List.foldr_map,
      hPremises]

-- ATTACH-BLOCKER: private declaration
private theorem folkProvable_closedPredCongBody {L : Language}
    (hL : L.hasEquality = true) (P : L.predSymbols)
    (ss ts : Fin (L.predArity P) → Term L) :
    folkProvable
      (Sequent.mk [closedPredCongAxiom hL P]
        [concretePredCongBody hL P ss ts]) := by
  rw [closedPredCongAxiom_eq_allList]
  rw [← captureSafePredCongBody]
  exact folkProvable_captureSafeAllListInstantiation
    (schematicPredCongBody hL P)
    (congruenceVars (L.predArity P))
    (congruenceTerms ss ts)
    (by rw [congruenceVars_length, congruenceTerms_length])
    (congruenceVars_nodup _)
    (schematicPredCongBody_bv_empty hL P)

-- ATTACH-BLOCKER: private declaration
private theorem captureSafeReflBody {L : Language}
    (hL : L.hasEquality = true) (t : Term L) :
    captureSafeAllListInstance
        (FormulaN.eq_ hL (.var 0) (.var 0)) [0] [t] =
      FormulaN.eq_ hL t t := by
  rw [captureSafeAllListInstance_eq_map _ _ _ rfl]
  simp only [formulaMapVars, termMapVars]
  have h := captureSafeSubst_var_at
    (FormulaN.eq_ hL (.var 0) (.var 0)) [0] [t]
    (by rfl) (by simp) 0 (by simp)
  simpa [captureSafeTermMap] using congrArg
    (fun u => FormulaN.eq_ hL u u) h

-- ATTACH-BLOCKER: private declaration
private theorem folkProvable_closedReflBody {L : Language}
    (hL : L.hasEquality = true) (t : Term L) :
    folkProvable
      (Sequent.mk [closedReflAxiom hL]
        [FormulaN.eq_ hL t t]) := by
  have h := folkProvable_captureSafeAllListInstantiation
    (FormulaN.eq_ hL (.var 0) (.var 0)) [0] [t]
    (by rfl) (by simp) (by rfl)
  rw [captureSafeReflBody] at h
  simpa [closedReflAxiom, FormulaN.allList] using h

-- ATTACH-BLOCKER: private declaration
private theorem eqCongBody_bv_empty {L : Language}
    (hL : L.hasEquality = true) :
    formulaBVN
      (eqCongruenceImplEq hL
        (.var 0) (.var 1) (.var 2) (.var 3)) = ∅ := by
  ext v
  simp [eqCongruenceImplEq, formulaBVN, Set.union, Set.empty]

-- ATTACH-BLOCKER: private declaration
set_option maxHeartbeats 2000000 in
private theorem captureSafeEqCongBody {L : Language}
    (hL : L.hasEquality = true)
    (s1 s2 t1 t2 : Term L) :
    captureSafeAllListInstance
        (eqCongruenceImplEq hL
          (.var 0) (.var 1) (.var 2) (.var 3))
        [0, 1, 2, 3] [s1, s2, t1, t2] =
      eqCongruenceImplEq hL s1 s2 t1 t2 := by
  let A :=
    eqCongruenceImplEq hL
      (.var 0) (.var 1) (.var 2) (.var 3)
  let vars := [0, 1, 2, 3]
  let us := [s1, s2, t1, t2]
  have h0 := captureSafeSubst_var_at A vars us
    (by rfl) (by simp [vars]) 0 (by simp [vars])
  have h1 := captureSafeSubst_var_at A vars us
    (by rfl) (by simp [vars]) 1 (by simp [vars])
  have h2 := captureSafeSubst_var_at A vars us
    (by rfl) (by simp [vars]) 2 (by simp [vars])
  have h3 := captureSafeSubst_var_at A vars us
    (by rfl) (by simp [vars]) 3 (by simp [vars])
  have hv0 :
      captureSafeTermMap A vars us 0 = s1 := by
    simpa [captureSafeTermMap, vars, us] using h0
  have hv1 :
      captureSafeTermMap A vars us 1 = s2 := by
    simpa [captureSafeTermMap, vars, us] using h1
  have hv2 :
      captureSafeTermMap A vars us 2 = t1 := by
    simpa [captureSafeTermMap, vars, us] using h2
  have hv3 :
      captureSafeTermMap A vars us 3 = t2 := by
    simpa [captureSafeTermMap, vars, us] using h3
  simp only [A, vars, us, eqCongruenceImplEq] at hv0 hv1 hv2 hv3
  rw [captureSafeAllListInstance_eq_map _ _ _
    (eqCongBody_bv_empty hL)]
  simp only [eqCongruenceImplEq, formulaMapVars, termMapVars]
  rw [hv0, hv1, hv2, hv3]

-- ATTACH-BLOCKER: private declaration
set_option maxHeartbeats 2000000 in
private theorem folkProvable_closedEqCongBody {L : Language}
    (hL : L.hasEquality = true)
    (s1 s2 t1 t2 : Term L) :
    folkProvable
      (Sequent.mk [closedEqCongAxiom hL]
        [eqCongruenceImplEq hL s1 s2 t1 t2]) := by
  have hInst :
      folkProvable
        (Sequent.mk
          [FormulaN.allList [0, 1, 2, 3]
            (eqCongruenceImplEq hL
              (.var 0) (.var 1) (.var 2) (.var 3))]
          [captureSafeAllListInstance
            (eqCongruenceImplEq hL
              (.var 0) (.var 1) (.var 2) (.var 3))
            [0, 1, 2, 3] [s1, s2, t1, t2]]) :=
    folkProvable_captureSafeAllListInstantiation
      (eqCongruenceImplEq hL
        (.var 0) (.var 1) (.var 2) (.var 3))
      [0, 1, 2, 3] [s1, s2, t1, t2]
      (by rfl) (by simp) (eqCongBody_bv_empty hL)
  rw [captureSafeEqCongBody] at hInst
  simpa only [closedEqCongAxiom] using hInst

-- ATTACH-BLOCKER: private declaration
private theorem folkCutFree_conjoinRight {L : Language}
    (Γ : List (FormulaN L)) (hd : FormulaN L)
    (tl : List (FormulaN L))
    (hhd : folkCutFreeProvable (Sequent.mk Γ [hd]))
    (htl : ∀ A ∈ tl,
      folkCutFreeProvable (Sequent.mk Γ [A])) :
    folkCutFreeProvable
      (Sequent.mk Γ [conjoinFormulae hd (hd :: tl)]) := by
  induction tl generalizing hd with
  | nil => simpa [conjoinFormulae] using hhd
  | cons A tl ih =>
    rw [conjoin_cons_cons]
    exact folkCutFree_andRight_end hd (conjoinFormulae A (A :: tl)) Γ [] hhd
      (ih A (htl A (List.mem_cons_self)) (fun B hB => htl B (List.mem_cons_of_mem A hB)))

-- ATTACH-BLOCKER: private declaration
private theorem folkCutFree_useImplicationBody {L : Language}
    (premises : List (FormulaN L)) (C : FormulaN L) :
    folkCutFreeProvable
      (Sequent.mk (implicationBody premises C :: premises) [C]) := by
  cases premises with
  | nil => simpa [implicationBody] using folkCutFree_axiom C
  | cons hd tl =>
      have hhd :
          folkCutFreeProvable (Sequent.mk (hd :: tl) [hd]) :=
        folkCutFree_shared_axiom _
          ⟨hd, List.Mem.head _, List.Mem.head _⟩
      have htl : ∀ A ∈ tl,
          folkCutFreeProvable (Sequent.mk (hd :: tl) [A]) := by
        intro A hA
        exact folkCutFree_shared_axiom _
          ⟨A, List.Mem.tail _ hA, List.Mem.head _⟩
      have hAnte :=
        folkCutFree_conjoinRight (hd :: tl) hd tl hhd htl
      simpa [implicationBody] using
        folkCutFree_implLeft_head
          (conjoinFormulae hd (hd :: tl)) C (hd :: tl)
          [] [] [C] hAnte (folkCutFree_axiom C)

-- ATTACH-BLOCKER: private declaration
private theorem folkProvable_useClosedBody {L : Language}
    (E : List (FormulaN L)) (closed body : FormulaN L)
    (premises : List (FormulaN L)) (C : FormulaN L)
    (hClosed : closed ∈ E)
    (hInst : folkProvable (Sequent.mk [closed] [body]))
    (hUse : folkCutFreeProvable
      (Sequent.mk (body :: premises) [C])) :
    folkProvable (Sequent.mk (E ++ premises) [C]) := by
  have hInstE : folkProvable (Sequent.mk E [body]) :=
    folkProvable_antecedentMono [closed] E [body]
      (by
        intro A hA
        simp only [List.mem_singleton] at hA
        subst A
        exact hClosed)
      hInst
  simpa using folkProvable_cut body E [] premises [C]
    hInstE (folkCutFreeProvable_to_folkProvable hUse)

-- ATTACH-BLOCKER: private declaration
private theorem folkCutFree_useEqCongBody {L : Language}
    (hL : L.hasEquality = true)
    (s1 s2 t1 t2 : Term L) :
    folkCutFreeProvable
      (Sequent.mk
        (eqCongruenceImplEq hL s1 s2 t1 t2 ::
          [FormulaN.eq_ hL s1 t1,
           FormulaN.eq_ hL s2 t2,
           FormulaN.eq_ hL s1 s2])
        [FormulaN.eq_ hL t1 t2]) := by
  let E1 := FormulaN.eq_ hL s1 t1
  let E2 := FormulaN.eq_ hL s2 t2
  let E3 := FormulaN.eq_ hL s1 s2
  let C := FormulaN.eq_ hL t1 t2
  let Γ := [E1, E2, E3]
  have h1 : folkCutFreeProvable (Sequent.mk Γ [E1]) :=
    folkCutFree_shared_axiom _
      ⟨E1, by simp [Γ], List.Mem.head _⟩
  have h2 : folkCutFreeProvable (Sequent.mk Γ [E2]) :=
    folkCutFree_shared_axiom _
      ⟨E2, by simp [Γ], List.Mem.head _⟩
  have h3 : folkCutFreeProvable (Sequent.mk Γ [E3]) :=
    folkCutFree_shared_axiom _
      ⟨E3, by simp [Γ], List.Mem.head _⟩
  have h23 :
      folkCutFreeProvable
        (Sequent.mk Γ [FormulaN.conj E2 E3]) := by
    simpa using folkCutFree_andRight_end E2 E3 Γ [] h2 h3
  have h123 :
      folkCutFreeProvable
        (Sequent.mk Γ
          [FormulaN.conj E1 (FormulaN.conj E2 E3)]) := by
    simpa using folkCutFree_andRight_end E1
      (FormulaN.conj E2 E3) Γ [] h1 h23
  simpa [eqCongruenceImplEq, E1, E2, E3, C, Γ] using
    folkCutFree_implLeft_head
      (FormulaN.conj E1 (FormulaN.conj E2 E3)) C Γ
      [] [] [C] h123 (folkCutFree_axiom C)

-- ATTACH-BLOCKER: private declaration
private theorem folkProvable_prependStep1 {L : Language}
    (pfx : List (FormulaN L))
    (hClosed : ∀ y F, F ∈ pfx → y ∉ formulaFVN F)
    {prem conc : Sequent L} (rule : FOLKStep1 prem conc)
    (h : folkProvable
      (Sequent.mk (pfx ++ prem.antecedent) prem.succedent)) :
    folkProvable
      (Sequent.mk (pfx ++ conc.antecedent) conc.succedent) := by
  cases rule with
  | weakenLeft A Γ Δ =>
      have h₁ := folkProvable_onePremise
        (.weakenLeft A (pfx ++ Γ) Δ) h
      exact folkProvable_antecedentMono
        (A :: pfx ++ Γ) (pfx ++ A :: Γ) Δ
          (by simp [or_assoc, or_left_comm, or_comm]) h₁
  | weakenRight A Γ Δ =>
      simpa [List.append_assoc] using
        folkProvable_onePremise
          (.weakenRight A (pfx ++ Γ) Δ) h
  | contractLeft A Γ Δ =>
      have h₀ : folkProvable
          (Sequent.mk (A :: A :: (pfx ++ Γ)) Δ) :=
        folkProvable_antecedentMono
          (pfx ++ A :: A :: Γ) (A :: A :: pfx ++ Γ) Δ
            (by simp [or_assoc, or_left_comm, or_comm]) h
      have h₁ := folkProvable_onePremise
        (.contractLeft A (pfx ++ Γ) Δ) h₀
      exact folkProvable_antecedentMono
        (A :: pfx ++ Γ) (pfx ++ A :: Γ) Δ
          (by simp [or_assoc, or_left_comm, or_comm]) h₁
  | contractRight A Γ Δ =>
      simpa [List.append_assoc] using
        folkProvable_onePremise
          (.contractRight A (pfx ++ Γ) Δ) h
  | exchangeLeft Γ A B Δ Λ =>
      have h' : folkProvable
          (Sequent.mk ((pfx ++ Γ) ++ [A, B] ++ Δ) Λ) := by
        simpa [List.append_assoc] using h
      simpa [List.append_assoc] using
        folkProvable_onePremise
          (.exchangeLeft (pfx ++ Γ) A B Δ Λ) h'
  | exchangeRight Γ Δ A B Λ =>
      simpa [List.append_assoc] using
        folkProvable_onePremise
          (.exchangeRight (pfx ++ Γ) Δ A B Λ) h
  | andLeftL A B Γ Δ =>
      have h₀ : folkProvable
          (Sequent.mk (A :: pfx ++ Γ) Δ) :=
        folkProvable_antecedentMono
          (pfx ++ A :: Γ) (A :: pfx ++ Γ) Δ
            (by simp [or_assoc, or_left_comm, or_comm]) h
      have h₁ := folkProvable_onePremise
        (.andLeftL A B (pfx ++ Γ) Δ) h₀
      exact folkProvable_antecedentMono
        (FormulaN.conj A B :: pfx ++ Γ)
        (pfx ++ FormulaN.conj A B :: Γ) Δ
          (by simp [or_assoc, or_left_comm, or_comm]) h₁
  | andLeftR A B Γ Δ =>
      have h₀ : folkProvable
          (Sequent.mk (B :: pfx ++ Γ) Δ) :=
        folkProvable_antecedentMono
          (pfx ++ B :: Γ) (B :: pfx ++ Γ) Δ
            (by simp [or_assoc, or_left_comm, or_comm]) h
      have h₁ := folkProvable_onePremise
        (.andLeftR A B (pfx ++ Γ) Δ) h₀
      exact folkProvable_antecedentMono
        (FormulaN.conj A B :: pfx ++ Γ)
        (pfx ++ FormulaN.conj A B :: Γ) Δ
          (by simp [or_assoc, or_left_comm, or_comm]) h₁
  | orRightL A B Γ Δ =>
      simpa [List.append_assoc] using
        folkProvable_onePremise
          (.orRightL A B (pfx ++ Γ) Δ) h
  | orRightR A B Γ Δ =>
      simpa [List.append_assoc] using
        folkProvable_onePremise
          (.orRightR A B (pfx ++ Γ) Δ) h
  | implRight A B Γ Δ =>
      have h₀ : folkProvable
          (Sequent.mk (A :: pfx ++ Γ) (Δ ++ [B])) :=
        folkProvable_antecedentMono
          (pfx ++ A :: Γ) (A :: pfx ++ Γ) (Δ ++ [B])
            (by simp [or_assoc, or_left_comm, or_comm]) h
      simpa [List.append_assoc] using
        folkProvable_onePremise
          (.implRight A B (pfx ++ Γ) Δ) h₀
  | negLeft A Γ Δ =>
      have h₁ := folkProvable_onePremise
        (.negLeft A (pfx ++ Γ) Δ) h
      exact folkProvable_antecedentMono
        (FormulaN.neg A :: pfx ++ Γ)
        (pfx ++ FormulaN.neg A :: Γ) Δ
          (by simp [or_assoc, or_left_comm, or_comm]) h₁
  | negRight A Γ Δ =>
      have h₀ : folkProvable
          (Sequent.mk (A :: pfx ++ Γ) Δ) :=
        folkProvable_antecedentMono
          (pfx ++ A :: Γ) (A :: pfx ++ Γ) Δ
            (by simp [or_assoc, or_left_comm, or_comm]) h
      simpa [List.append_assoc] using
        folkProvable_onePremise
          (.negRight A (pfx ++ Γ) Δ) h₀
  | allLeft t x A Γ Δ hFree =>
      have h₀ : folkProvable
          (Sequent.mk
            (formulaSubstN A t x :: pfx ++ Γ) Δ) :=
        folkProvable_antecedentMono
          (pfx ++ formulaSubstN A t x :: Γ)
          (formulaSubstN A t x :: pfx ++ Γ) Δ
            (by simp [or_assoc, or_left_comm, or_comm]) h
      have h₁ := folkProvable_onePremise
        (.allLeft t x A (pfx ++ Γ) Δ hFree) h₀
      exact folkProvable_antecedentMono
        (FormulaN.all x A :: pfx ++ Γ)
        (pfx ++ FormulaN.all x A :: Γ) Δ
          (by simp [or_assoc, or_left_comm, or_comm]) h₁
  | allRight y x A Γ Δ hFresh hFree =>
      have hFresh' :
          ∀ F ∈
              (Sequent.mk (pfx ++ Γ)
                (Δ ++ [FormulaN.all x A])).antecedent ++
              (Sequent.mk (pfx ++ Γ)
                (Δ ++ [FormulaN.all x A])).succedent,
            y ∉ formulaFVN F := by
        intro F hF
        rcases List.mem_append.mp hF with hAnte | hSucc
        · rcases List.mem_append.mp hAnte with hPfx | hΓ
          · exact hClosed y F hPfx
          · exact hFresh F (List.mem_append_left _ hΓ)
        · exact hFresh F (List.mem_append_right _ hSucc)
      simpa [List.append_assoc] using
        folkProvable_onePremise
          (.allRight y x A (pfx ++ Γ) Δ hFresh' hFree) h
  | exLeft y x A Γ Δ hFresh hFree =>
      have h₀ : folkProvable
          (Sequent.mk
            (formulaSubstN A (.var y) x :: pfx ++ Γ) Δ) :=
        folkProvable_antecedentMono
          (pfx ++ formulaSubstN A (.var y) x :: Γ)
          (formulaSubstN A (.var y) x :: pfx ++ Γ) Δ
            (by simp [or_assoc, or_left_comm, or_comm]) h
      have hFresh' :
          ∀ F ∈
              (Sequent.mk
                (FormulaN.ex x A :: pfx ++ Γ) Δ).antecedent ++
              (Sequent.mk
                (FormulaN.ex x A :: pfx ++ Γ) Δ).succedent,
            y ∉ formulaFVN F := by
        intro F hF
        rcases List.mem_append.mp hF with hAnte | hΔ
        · rcases List.mem_cons.mp hAnte with rfl | hRest
          · exact hFresh _ (List.mem_append_left _ (List.Mem.head _))
          · rcases List.mem_append.mp hRest with hPfx | hΓ
            · exact hClosed y F hPfx
            · exact hFresh F
                (List.mem_append_left _
                  (List.mem_cons_of_mem _ hΓ))
        · exact hFresh F (List.mem_append_right _ hΔ)
      have h₁ := folkProvable_onePremise
        (.exLeft y x A (pfx ++ Γ) Δ hFresh' hFree) h₀
      exact folkProvable_antecedentMono
        (FormulaN.ex x A :: pfx ++ Γ)
        (pfx ++ FormulaN.ex x A :: Γ) Δ
          (by simp [or_assoc, or_left_comm, or_comm]) h₁
  | exRight t x A Γ Δ hFree =>
      simpa [List.append_assoc] using
        folkProvable_onePremise
          (.exRight t x A (pfx ++ Γ) Δ hFree) h

-- ATTACH-BLOCKER: private declaration
private theorem folkProvable_prependStep2 {L : Language}
    (pfx : List (FormulaN L))
    {prem₁ prem₂ conc : Sequent L}
    (rule : FOLKStep2 prem₁ prem₂ conc)
    (h₁ : folkProvable
      (Sequent.mk (pfx ++ prem₁.antecedent) prem₁.succedent))
    (h₂ : folkProvable
      (Sequent.mk (pfx ++ prem₂.antecedent) prem₂.succedent)) :
    folkProvable
      (Sequent.mk (pfx ++ conc.antecedent) conc.succedent) := by
  cases rule with
  | cut A Γ Δ Λ Θ =>
      have h₂' : folkProvable
          (Sequent.mk (A :: pfx ++ Λ) Θ) :=
        folkProvable_antecedentMono
          (pfx ++ A :: Λ) (A :: pfx ++ Λ) Θ
            (by simp [or_assoc, or_left_comm, or_comm]) h₂
      have hCut := folkProvable_twoPremise
        (.cut A (pfx ++ Γ) Δ (pfx ++ Λ) Θ) h₁ h₂'
      exact folkProvable_antecedentMono
        ((pfx ++ Γ) ++ (pfx ++ Λ))
        (pfx ++ (Γ ++ Λ)) (Δ ++ Θ)
        (by simp [or_assoc, or_left_comm, or_comm]) hCut
  | andRight A B Γ Δ =>
      simpa [List.append_assoc] using
        folkProvable_twoPremise
          (.andRight A B (pfx ++ Γ) Δ) h₁ h₂
  | orLeft A B Γ Δ =>
      have h₁' : folkProvable
          (Sequent.mk (A :: pfx ++ Γ) Δ) :=
        folkProvable_antecedentMono
          (pfx ++ A :: Γ) (A :: pfx ++ Γ) Δ
            (by simp [or_assoc, or_left_comm, or_comm]) h₁
      have h₂' : folkProvable
          (Sequent.mk (B :: pfx ++ Γ) Δ) :=
        folkProvable_antecedentMono
          (pfx ++ B :: Γ) (B :: pfx ++ Γ) Δ
            (by simp [or_assoc, or_left_comm, or_comm]) h₂
      have hOr := folkProvable_twoPremise
        (.orLeft A B (pfx ++ Γ) Δ) h₁' h₂'
      exact folkProvable_antecedentMono
        (FormulaN.disj A B :: pfx ++ Γ)
        (pfx ++ FormulaN.disj A B :: Γ) Δ
          (by simp [or_assoc, or_left_comm, or_comm]) hOr
  | implLeft A B Γ Δ Λ Θ =>
      have h₂' : folkProvable
          (Sequent.mk (B :: pfx ++ Λ) Θ) :=
        folkProvable_antecedentMono
          (pfx ++ B :: Λ) (B :: pfx ++ Λ) Θ
            (by simp [or_assoc, or_left_comm, or_comm]) h₂
      have hImpl := folkProvable_twoPremise
        (.implLeft A B (pfx ++ Γ) Δ (pfx ++ Λ) Θ) h₁ h₂'
      exact folkProvable_antecedentMono
        (FormulaN.impl A B :: (pfx ++ Γ) ++ (pfx ++ Λ))
        (pfx ++ FormulaN.impl A B :: (Γ ++ Λ)) (Δ ++ Θ)
        (by simp [or_assoc, or_left_comm, or_comm]) hImpl

-- ATTACH-BLOCKER: private declaration
private theorem rootSupportedLKeProof_replay
    {L : Language}
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (S : Sequent L) (pfx : List (FormulaN L))
    (hClosed : ∀ y F, F ∈ pfx → y ∉ formulaFVN F)
    (hLeaf : ∀ (hEq : L.hasEquality = true)
      (ax : LKeEqualityAxiom L),
      equalityAxiomSupportedBy S ax →
      folkProvable
        (Sequent.mk (pfx ++ (ax.toSequent hEq).antecedent)
          (ax.toSequent hEq).succedent)) :
    {q : Sequent L} → RootSupportedLKeProof S q →
      folkProvable
        (Sequent.mk (pfx ++ q.antecedent) q.succedent)
  | _, .axiom_ q hAx =>
      folkProvable_weakenLeftList pfx q.antecedent q.succedent
        ⟨.axiom_ q hAx⟩
  | _, .eqAxiom hEq ax hAx =>
      hLeaf hEq ax hAx
  | _, .onePremise rule t =>
      folkProvable_prependStep1 pfx hClosed rule
        (rootSupportedLKeProof_replay S pfx hClosed hLeaf t)
  | _, .twoPremise rule t₁ t₂ =>
      folkProvable_prependStep2 pfx rule
        (rootSupportedLKeProof_replay S pfx hClosed hLeaf t₁)
        (rootSupportedLKeProof_replay S pfx hClosed hLeaf t₂)

-- ===================================================================
-- Helpers: syntactic closedness of the equality-axiom prefix
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem quantifyAll_fv_sub {L : Language} (start count : Nat)
    (inner : FormulaN L) (v : Nat)
    (hv : formulaFVN
      ((List.range count).foldr
        (fun i acc => FormulaN.all (start + i) acc) inner) v) :
    formulaFVN inner v := by
-- BEGIN PROOF
  induction count generalizing inner with
  | zero => simp only [List.range_zero, List.foldr_nil] at hv; exact hv
  | succ n ih =>
    simp only [List.range_succ, List.foldr_append, List.foldr_cons,
      List.foldr_nil] at hv
    have hAll := ih (FormulaN.all (start + n) inner) hv
    exact hAll.1

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem quantifyAll_binds {L : Language} (start count : Nat)
    (inner : FormulaN L) (k : Nat) (hk : k < count) :
    ¬ formulaFVN
      ((List.range count).foldr
        (fun i acc => FormulaN.all (start + i) acc) inner)
      (start + k) := by
-- BEGIN PROOF
  induction count generalizing inner with
  | zero => exact absurd hk (Nat.not_lt_zero _)
  | succ n ih =>
    simp only [List.range_succ, List.foldr_append, List.foldr_cons,
      List.foldr_nil]
    intro hFV
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
    · exact ih (FormulaN.all (start + n) inner) hlt hFV
    · subst heq
      have hAll := quantifyAll_fv_sub start k
        (FormulaN.all (start + k) inner) (start + k) hFV
      exact hAll.2 rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem fv_subset_range_closed {L : Language} (start count : Nat)
    (inner : FormulaN L)
    (h : ∀ v, formulaFVN inner v →
      ∃ k, k < count ∧ v = start + k) :
    formulaFVN
      ((List.range count).foldr
        (fun i acc => FormulaN.all (start + i) acc) inner) = ∅ := by
-- BEGIN PROOF
  ext v
  constructor
  · intro hv
    have hInner := quantifyAll_fv_sub start count inner v hv
    obtain ⟨k, hk, hveq⟩ := h v hInner
    subst hveq
    exact absurd hv (quantifyAll_binds start count inner k hk)
  · intro hv
    exact hv.elim

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem doubleQuantifyAll_closed {L : Language} (n : Nat)
    (inner : FormulaN L)
    (h : ∀ v, formulaFVN inner v → v < 2 * n) :
    formulaFVN
      ((List.range n).foldr
        (fun i acc => FormulaN.all (0 + i) acc)
        ((List.range n).foldr
          (fun i acc => FormulaN.all (n + i) acc) inner)) = ∅ := by
-- BEGIN PROOF
  apply fv_subset_range_closed
  intro v hv
  have hInner := quantifyAll_fv_sub n n inner v hv
  have hLt := h v hInner
  by_cases hvLt : v < n
  · exact ⟨v, hvLt, by omega⟩
  · exfalso
    have heq : v = n + (v - n) := by omega
    rw [heq] at hv
    exact quantifyAll_binds n n inner (v - n) (by omega) hv

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem conjoin_fv_bound {L : Language} (bound : Nat)
    (hd : FormulaN L) (tl : List (FormulaN L))
    (h : ∀ A ∈ hd :: tl, ∀ v, formulaFVN A v → v < bound) :
    ∀ v, formulaFVN (conjoinFormulae hd (hd :: tl)) v →
      v < bound := by
  induction tl generalizing hd with
  | nil => exact fun v hv => h hd List.mem_cons_self v hv
  | cons x xs ih =>
    intro v hv
    rw [conjoin_cons_cons] at hv
    rcases hv with hh | ht
    · exact h hd List.mem_cons_self v hh
    · exact ih x (fun A hA => h A (List.mem_cons_of_mem hd hA)) v ht

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem eqPairs_fv_bound {L : Language}
    (hL : L.hasEquality = true) (n : Nat) :
    ∀ A ∈ (List.finRange n).map
        (fun (i : Fin n) =>
          FormulaN.eq_ hL
            (Term.var (i : Nat) : Term L)
            (Term.var (n + (i : Nat)))),
      ∀ v, formulaFVN A v → v < 2 * n := by
-- BEGIN PROOF
  intro A hA v hv
  rw [List.mem_map] at hA
  obtain ⟨i, _, rfl⟩ := hA
  rcases hv with
    (hi : v = (i : Nat)) | (hj : v = n + (i : Nat))
  · rw [hi]
    omega
  · rw [hj]
    omega

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem eq_func_fv_bound {L : Language}
    (hL : L.hasEquality = true) (f : L.funSymbols) :
    let n := L.funArity f
    ∀ v,
      formulaFVN
        (FormulaN.eq_ hL
          (Term.func f
            (fun (i : Fin n) => Term.var (i : Nat)))
          (Term.func f
            (fun (i : Fin n) => Term.var (n + (i : Nat))))) v →
        v < 2 * n := by
-- BEGIN PROOF
  intro n v hv
  rcases hv with
    ⟨i, (hi : v = (i : Nat))⟩ |
      ⟨i, (hi : v = n + (i : Nat))⟩
  · rw [hi]
    omega
  · rw [hi]
    omega

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem predN_ys_fv_bound {L : Language} (P : L.predSymbols) :
    let n := L.predArity P
    ∀ v,
      formulaFVN
        (FormulaN.predN P
          (fun (i : Fin n) => Term.var (n + (i : Nat)))) v →
        v < 2 * n := by
-- BEGIN PROOF
  intro n v hv
  simp only [formulaFVN] at hv
  obtain ⟨j, hj⟩ := hv
  simp only [termFV, Set.singleton] at hj
  rw [hj]
  omega

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem predN_xs_fv_bound {L : Language} (P : L.predSymbols) :
    let n := L.predArity P
    ∀ v,
      formulaFVN
        (FormulaN.predN P
          (fun (i : Fin n) => Term.var (i : Nat))) v →
        v < 2 * n := by
-- BEGIN PROOF
  intro n v hv
  simp only [formulaFVN] at hv
  obtain ⟨j, hj⟩ := hv
  simp only [termFV, Set.singleton] at hj
  rw [hj]
  omega

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem premises_fv_bound {L : Language}
    (hL : L.hasEquality = true) (P : L.predSymbols) :
    let n := L.predArity P
    ∀ A ∈
        (List.finRange n).map
            (fun (i : Fin n) =>
              FormulaN.eq_ hL
                (Term.var (i : Nat) : Term L)
                (Term.var (n + (i : Nat)))) ++
          [FormulaN.predN P
            (fun (i : Fin n) => Term.var (i : Nat))],
      ∀ v, formulaFVN A v → v < 2 * n := by
-- BEGIN PROOF
  intro n A hA v hv
  rcases List.mem_append.mp hA with hEq | hPred
  · exact eqPairs_fv_bound hL n A hEq v hv
  · simp only [List.mem_singleton] at hPred
    subst hPred
    exact predN_xs_fv_bound P v hv

-- ATTACH-BLOCKER: scoped helper requires manual relocation
set_option maxHeartbeats 800000 in
theorem closedFunCongAxiom_closed {L : Language}
    (hL : L.hasEquality = true) (f : L.funSymbols) :
    formulaFVN (closedFunCongAxiom hL f) = ∅ := by
-- BEGIN PROOF
  unfold closedFunCongAxiom
  simp only []
  apply doubleQuantifyAll_closed
  intro v hv
  split at hv
  · exact eq_func_fv_bound hL f v hv
  · rcases hv with hAnte | hCons
    · split at hAnte
      · exact eq_func_fv_bound hL f v hAnte
      · next hd' tl' heq' =>
        exact conjoin_fv_bound _ hd' tl' (by
          intro A hA w hw
          exact eqPairs_fv_bound hL _ A
            (by
              rw [heq']
              exact hA) w hw) v hAnte
    · exact eq_func_fv_bound hL f v hCons

-- ATTACH-BLOCKER: scoped helper requires manual relocation
set_option maxHeartbeats 800000 in
theorem closedPredCongAxiom_closed {L : Language}
    (hL : L.hasEquality = true) (P : L.predSymbols) :
    formulaFVN (closedPredCongAxiom hL P) = ∅ := by
-- BEGIN PROOF
  unfold closedPredCongAxiom
  simp only []
  apply doubleQuantifyAll_closed
  intro v hv
  split at hv
  · exact predN_ys_fv_bound P v hv
  · rcases hv with hAnte | hCons
    · split at hAnte
      · exact predN_ys_fv_bound P v hAnte
      · next hd' tl' heq' =>
        exact conjoin_fv_bound _ hd' tl' (by
          intro A hA w hw
          exact premises_fv_bound hL P A
            (by
              rw [heq']
              exact hA) w hw) v hAnte
    · exact predN_ys_fv_bound P v hCons

-- retained: used by LCS.CutElim.Interpolation.Equality.Reduction
theorem closedEqCongAxiom_closed {L : Language}
    (hL : L.hasEquality = true) :
    formulaFVN (closedEqCongAxiom (L := L) hL) = ∅ := by
-- BEGIN PROOF
  ext v
  simp [closedEqCongAxiom, formulaFV_allList_iff,
    eqCongruenceImplEq, formulaFVN, termFV,
    Set.union, Set.singleton, Set.empty]
  omega

-- ===================================================================
-- Lemma 6.5.3 (companion theorem): equality_axiom_derivable_from_se
-- ===================================================================

-- ATTACH-BLOCKER: private name in relocated declaration
/-- Lemma 6.5.3 (companion): For every equality axiom
Gamma' -> Delta' used in an LKe-proof of S, the sequent
(closedEqualityAxioms S ++ Gamma') -> Delta' is LK-provable. Each
equality axiom instance is derivable from the corresponding closed
equality axiom in S_e via universal instantiation.
Requires that the axiom's function/predicate head (including equality) appears in S
(so the closed axiom is in closedEqualityAxioms S). -/
theorem equality_axiom_derivable_from_se {L : Language} (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (S : Sequent L)
    (ax : LKeEqualityAxiom L)
    (hAxSyms : match ax with
      | .refl _ => True
      | .funcCong f _ _ => f ∈ sequentFunSymbolsList S
      | .predCong P _ _ => P ∈ sequentPredSymbolsList S
      | .eqCong _ _ _ _ => sequentHasEq S = true) :
    folkProvable
      { antecedent := closedEqualityAxioms hL S ++
          (ax.toSequent hL).antecedent
        succedent := (ax.toSequent hL).succedent } :=
-- BEGIN PROOF
by
  let E := closedEqualityAxioms hL S
  cases ax with
  | refl t =>
      simp only [LKeEqualityAxiom.toSequent, List.append_nil]
      exact folkProvable_antecedentMono
        [closedReflAxiom hL] E [FormulaN.eq_ hL t t]
        (by
          intro A hA
          simp only [List.mem_singleton] at hA
          subst A
          simp [E, closedEqualityAxioms])
        (folkProvable_closedReflBody hL t)
  | funcCong f ss ts =>
      change f ∈ sequentFunSymbolsList S at hAxSyms
      simp only [LKeEqualityAxiom.toSequent]
      simpa [concreteFunCongBody, concreteEqPairs] using
        folkProvable_useClosedBody E
          (closedFunCongAxiom hL f)
          (concreteFunCongBody hL f ss ts)
          (concreteEqPairs hL ss ts)
          (FormulaN.eq_ hL
            (Term.func f ss) (Term.func f ts))
          (closedFunCongAxiom_mem_se hL S f hAxSyms)
          (folkProvable_closedFunCongBody hL f ss ts)
          (folkCutFree_useImplicationBody
            (concreteEqPairs hL ss ts)
            (FormulaN.eq_ hL
              (Term.func f ss) (Term.func f ts)))
  | predCong P ss ts =>
      change P ∈ sequentPredSymbolsList S at hAxSyms
      simp only [LKeEqualityAxiom.toSequent]
      simpa [concretePredCongBody, concretePredCongPremises,
        concreteEqPairs] using
        folkProvable_useClosedBody E
          (closedPredCongAxiom hL P)
          (concretePredCongBody hL P ss ts)
          (concretePredCongPremises hL P ss ts)
          (FormulaN.predN P ts)
          (closedPredCongAxiom_mem_se hL S P hAxSyms)
          (folkProvable_closedPredCongBody hL P ss ts)
          (folkCutFree_useImplicationBody
            (concretePredCongPremises hL P ss ts)
            (FormulaN.predN P ts))
  | eqCong s1 s2 t1 t2 =>
      simp only [LKeEqualityAxiom.toSequent]
      simpa using
        folkProvable_useClosedBody E
          (closedEqCongAxiom hL)
          (eqCongruenceImplEq hL s1 s2 t1 t2)
          [FormulaN.eq_ hL s1 t1,
           FormulaN.eq_ hL s2 t2,
           FormulaN.eq_ hL s1 s2]
          (FormulaN.eq_ hL t1 t2)
          (closedEqCongAxiom_mem_se hL S hAxSyms)
          (folkProvable_closedEqCongBody hL s1 s2 t1 t2)
          (folkCutFree_useEqCongBody hL s1 s2 t1 t2)

-- ===================================================================
-- Lemma 6.5.3 (companion theorem): lke_to_lk_with_se
-- ===================================================================

/-- Lemma 6.5.3 (companion): Forward direction: if S is
LKe-provable, then (closedEqualityAxioms S ++ Gamma) -> Delta
is LK-provable (folkProvable). The textbook states the right side
as "LK-provable": the closed equality axioms S_e are universally
valid, so S_e, Gamma -> Delta is provable in LK (without equality
axioms) by instantiating the closed axioms. -/
theorem lke_to_folk_with_se {L : Language} (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (S : Sequent L)
    (hProv : lkeProvable S) :
    folkProvable
      { antecedent := closedEqualityAxioms hL S ++ S.antecedent
        succedent := S.succedent } := by
  -- REPAIR(T6-47): proof pending
  sorry

-- ===================================================================
-- Lemma 6.5.3 (companion theorem): lke_with_se_to_lke
-- ===================================================================





-- ===================================================================
-- Lemma 6.5.3: lke_provable_iff_lke_with_se
-- ===================================================================

/-- Lemma 6.5.3: A sequent S = Gamma -> Delta is LKe-provable
iff S_e, Gamma -> Delta is LK-provable (folkProvable). The
forward direction adds the universally valid closed equality
axioms to the antecedent and produces an LK proof. The backward
direction wraps the LK proof in LKe and strips the S_e prefix
using lkeProvable_remove_valid_prefix. -/
@[blueprint "chap6__lemma_6_5_3" (main := true)]
theorem lke_provable_iff_lke_with_se {L : Language} (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (S : Sequent L) :
    lkeProvable S ↔
    folkProvable
      { antecedent := closedEqualityAxioms hL S ++ S.antecedent
        succedent := S.succedent } 

-- ===================================================================
-- Lemma 6.5.4 (required type): LKeBotProofTree
-- ===================================================================

/-- Proof trees for LKₑ,⊥, indexed by their conclusion sequent.
The system has the ordinary LK axioms and rules, equality-axiom leaves,
and the falsum axiom ⊥ →. The designated nullary predicate represents
the genuine logical constant ⊥. -/
@[blueprint "chap6__lemma_6_5_4"]
inductive LKeBotProofTree {L : Language} (hL : L.hasEquality = true)
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0) : Sequent L → Type where
  /-- Ordinary LK axiom leaf. -/
  | axiom_ (s : Sequent L) (h : isFOLKAxiom s) :
      LKeBotProofTree hL botP hBotArity s
  /-- Equality axiom leaf. -/
  | eqAxiom (ax : LKeEqualityAxiom L) :
      LKeBotProofTree hL botP hBotArity (ax.toSequent hL)
  /-- The falsum axiom ⊥ →. -/
  | botAxiom :
      LKeBotProofTree hL botP hBotArity (Sequent.mk [botFormula botP hBotArity] [])
  /-- One-premise LK rule above an LKₑ,⊥ subproof. -/
  | onePremise {prem conc : Sequent L} (rule : FOLKStep1 prem conc)
      (t : LKeBotProofTree hL botP hBotArity prem) :
      LKeBotProofTree hL botP hBotArity conc
  /-- Two-premise LK rule above LKₑ,⊥ subproofs, including cut. -/
  | twoPremise {prem1 prem2 conc : Sequent L} (rule : FOLKStep2 prem1 prem2 conc)
      (t1 : LKeBotProofTree hL botP hBotArity prem1)
      (t2 : LKeBotProofTree hL botP hBotArity prem2) :
      LKeBotProofTree hL botP hBotArity conc

/-- A sequent is LKₑ,⊥-provable if it has an LKₑ,⊥ proof tree. -/
@[blueprint "chap6__lemma_6_5_4"]
def lkeBotProvable {L : Language} (hL : L.hasEquality = true)
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0) (s : Sequent L) : Prop :=
  Nonempty (LKeBotProofTree hL botP hBotArity s)

-- ===================================================================
-- Lemma 6.5.4 (required def): formulaNonEqPredSymbols
-- ===================================================================

/-- Lemma 6.5.4 (required): The set of predicate symbols occurring
in a formula, excluding the equality symbol. For FormulaN, equality
is a built-in constructor (not a predicate symbol), so this is
simply the set of all predicate symbols in the formula. -/
@[blueprint "chap6__lemma_6_5_4"]
def formulaNonEqPredSymbols {L : Language}
    (A : FormulaN L) : Set L.predSymbols :=
  formulaPredSymbolsN A

-- ===================================================================
-- Lemma 6.5.4 (helper def): listFormulaNonEqPredSymbols
-- ===================================================================

/-- Lemma 6.5.4 (helper): The set of non-equality predicate
symbols occurring in a list of formulae. -/
@[blueprint "chap6__lemma_6_5_4"]
def listFormulaNonEqPredSymbols {L : Language}
    (fs : List (FormulaN L)) : Set L.predSymbols :=
  fun P => ∃ A ∈ fs, formulaNonEqPredSymbols A P

-- ===================================================================
-- Lemma 6.5.4 (required def): closedEqualityAxiomsForSide
-- ===================================================================

-- retained: used by LCS.CutElim.Interpolation.Equality.Reduction
/-- Lemma 6.5.4 (required): Given lists Gamma_i and Delta_i,
returns the closed equality axioms for the function and predicate
symbols occurring in Gamma_i union Delta_i (a subset of S_e).
This computes S_e^1 or S_e^2 depending on which side of the
partition is given. Equality congruence is included only when equality
occurs on that side. -/
def closedEqualityAxiomsForSide {L : Language} (hL : L.hasEquality = true)
    [DecidableEq L.funSymbols] [DecidableEq L.predSymbols]
    (gamma delta : List (FormulaN L)) : List (FormulaN L) :=
  let side : Sequent L :=
    { antecedent := gamma, succedent := delta }
  [closedReflAxiom hL] ++
  (sequentFunSymbolsList side).map (closedFunCongAxiom hL) ++
  ((sequentPredSymbolsList side).map (closedPredCongAxiom hL) ++
    (if sequentHasEq side then [closedEqCongAxiom hL] else []))

-- ===================================================================
-- Lemma 6.5.4 (required def): replaceBotByNegRefl
-- ===================================================================

-- retained: used by LCS.CutElim.Interpolation.Equality.Reduction
/-- Lemma 6.5.4 (required): Replaces all occurrences of bot
(falsum, encoded as `predN botP _`) in formula C by
¬∀z(z = z), where z is the given fresh variable. -/
noncomputable def replaceBotByNegRefl {L : Language} (hL : L.hasEquality = true)
    (botP : L.predSymbols) (_hBotArity : L.predArity botP = 0)
    (C : FormulaN L) (z : Nat) : FormulaN L :=
  open Classical in
  match C with
  | .predN Q args =>
    if Q = botP then
      FormulaN.neg (FormulaN.all z (FormulaN.eq_ hL (Term.var z) (Term.var z)))
    else .predN Q args
  | .eq_ h t1 t2 => .eq_ h t1 t2
  | .conj A B =>
    FormulaN.conj (replaceBotByNegRefl hL botP _hBotArity A z)
      (replaceBotByNegRefl hL botP _hBotArity B z)
  | .disj A B =>
    FormulaN.disj (replaceBotByNegRefl hL botP _hBotArity A z)
      (replaceBotByNegRefl hL botP _hBotArity B z)
  | .impl A B =>
    FormulaN.impl (replaceBotByNegRefl hL botP _hBotArity A z)
      (replaceBotByNegRefl hL botP _hBotArity B z)
  | .neg A => FormulaN.neg (replaceBotByNegRefl hL botP _hBotArity A z)
  | .all x A => FormulaN.all x (replaceBotByNegRefl hL botP _hBotArity A z)
  | .ex x A => FormulaN.ex x (replaceBotByNegRefl hL botP _hBotArity A z)

-- ===================================================================
-- Lemma 6.5.4 (required structure): IsLKeInterpolant
-- ===================================================================

/-- Lemma 6.5.4 (required): A formula C is an interpolant of a
partition <Gamma_1, Delta_1, Gamma_2, Delta_2> of an LKₑ-provable
sequent if: (i) Gamma_1 -> Delta_1, C and C, Gamma_2 -> Delta_2
are LKₑ-provable, and (ii) all predicate symbols (except equality),
constant symbols, and free variables in C occur both in
Gamma_1 union Delta_1 and in Gamma_2 union Delta_2. -/
@[blueprint "chap6__lemma_6_5_4"]
structure IsLKeInterpolant {L : Language} (hL : L.hasEquality = true)
    (botP : L.predSymbols) (hBotArity : L.predArity botP = 0) {s : Sequent L}
    (p : SequentPartition s) (C : FormulaN L) : Prop where
  /-- Gamma_1 -> Delta_1, C is LKₑ-provable -/
  left_lke_provable :
    lkeProvable
      { antecedent := p.gamma1
        succedent := p.delta1 ++ [C] }
  /-- C, Gamma_2 -> Delta_2 is LKₑ-provable -/
  right_lke_provable :
    lkeProvable
      { antecedent := [C] ++ p.gamma2
        succedent := p.delta2 }
  /-- All predicate symbols in C other than equality occur in both sides
      of the partition (OD-A20). Equality is a separate constructor;
      the designated nullary predicate botP is included in this condition. -/
  pred_common_except_eq :
    ∀ P, formulaNonEqPredSymbols C P →
      listFormulaNonEqPredSymbols (p.gamma1 ++ p.delta1) P ∧
      listFormulaNonEqPredSymbols (p.gamma2 ++ p.delta2) P
  /-- All constant symbols in C occur in both sides of the
      partition -/
  const_common :
    formulaConstSymbolsN C ⊆
      listFormulaConstSymbols (p.gamma1 ++ p.delta1) ∩
      listFormulaConstSymbols (p.gamma2 ++ p.delta2)
  /-- All free variables in C occur in both sides of the
      partition -/
  fv_common :
    formulaFVN C ⊆
      listFormulaFV (p.gamma1 ++ p.delta1) ∩
      listFormulaFV (p.gamma2 ++ p.delta2)

-- ===================================================================
-- Lemma 6.5.4 (companion theorem): se_partition_union
-- ===================================================================



end LCS.CutElim.Interpolation.Equality
end

