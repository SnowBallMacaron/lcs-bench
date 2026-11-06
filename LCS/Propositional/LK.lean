import LCS.Item
import LCS.Util
import LCS.Propositional.Systems.G
import LCS.Propositional.Infinite
import Attach
import LCS.Propositional.LK.ProofsStamp

/-! # Propositional.LK
    Formalization of Chapter 3, Sections 3.6.1-3.6.5.
    Defines the Gentzen system LK', proves equivalence with G',
    Gentzen's Hauptsatz (cut elimination), and consistency
    characterization in LK'.
-/

namespace LCS.Propositional.LK

open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

-- ========= Definition 3.6.1: Gentzen System LK' (indexed) =========

/-- Definition 3.6.1: One-premise rules of LK' (structural: weakening,
    contraction, exchange; logical: and-left1/2, or-right1/2, impl-right, neg). -/
@[blueprint "chap3__definition_3_6_1" (main := true)]
inductive LKStep1 : Sequent → Sequent → Type where
  | weakenLeft (Γ Δ : List PropFormulaNormalized) (A : PropFormulaNormalized) :
      LKStep1 (Sequent.mk Γ Δ)
              (Sequent.mk (A :: Γ) Δ)
  | weakenRight (Γ Δ : List PropFormulaNormalized) (A : PropFormulaNormalized) :
      LKStep1 (Sequent.mk Γ Δ)
              (Sequent.mk Γ (A :: Δ))
  | contractLeft (Γ₁ Γ₂ Δ : List PropFormulaNormalized) (A : PropFormulaNormalized) :
      LKStep1 (Sequent.mk (Γ₁ ++ A :: A :: Γ₂) Δ)
              (Sequent.mk (Γ₁ ++ A :: Γ₂) Δ)
  | contractRight (Γ Δ₁ Δ₂ : List PropFormulaNormalized) (A : PropFormulaNormalized) :
      LKStep1 (Sequent.mk Γ (Δ₁ ++ A :: A :: Δ₂))
              (Sequent.mk Γ (Δ₁ ++ A :: Δ₂))
  | exchangeLeft (Γ₁ Γ₂ Δ : List PropFormulaNormalized) (A B : PropFormulaNormalized) :
      LKStep1 (Sequent.mk (Γ₁ ++ A :: B :: Γ₂) Δ)
              (Sequent.mk (Γ₁ ++ B :: A :: Γ₂) Δ)
  | exchangeRight (Γ Δ₁ Δ₂ : List PropFormulaNormalized) (A B : PropFormulaNormalized) :
      LKStep1 (Sequent.mk Γ (Δ₁ ++ A :: B :: Δ₂))
              (Sequent.mk Γ (Δ₁ ++ B :: A :: Δ₂))
  | andLeft1 (Γ Δ : List PropFormulaNormalized) (A B : PropFormulaNormalized) :
      LKStep1 (Sequent.mk (A :: Γ) Δ)
              (Sequent.mk (PropFormulaNormalized.conj A B :: Γ) Δ)
  | andLeft2 (Γ Δ : List PropFormulaNormalized) (A B : PropFormulaNormalized) :
      LKStep1 (Sequent.mk (B :: Γ) Δ)
              (Sequent.mk (PropFormulaNormalized.conj A B :: Γ) Δ)
  | orRight1 (Γ Δ : List PropFormulaNormalized) (A B : PropFormulaNormalized) :
      LKStep1 (Sequent.mk Γ (A :: Δ))
              (Sequent.mk Γ (PropFormulaNormalized.disj A B :: Δ))
  | orRight2 (Γ Δ : List PropFormulaNormalized) (A B : PropFormulaNormalized) :
      LKStep1 (Sequent.mk Γ (B :: Δ))
              (Sequent.mk Γ (PropFormulaNormalized.disj A B :: Δ))
  | implRight (Γ Δ : List PropFormulaNormalized) (A B : PropFormulaNormalized) :
      LKStep1 (Sequent.mk (A :: Γ) (B :: Δ))
              (Sequent.mk Γ (PropFormulaNormalized.impl A B :: Δ))
  | negLeft (Γ Δ : List PropFormulaNormalized) (A : PropFormulaNormalized) :
      LKStep1 (Sequent.mk Γ (A :: Δ))
              (Sequent.mk (PropFormulaNormalized.neg A :: Γ) Δ)
  | negRight (Γ Δ : List PropFormulaNormalized) (A : PropFormulaNormalized) :
      LKStep1 (Sequent.mk (A :: Γ) Δ)
              (Sequent.mk Γ (PropFormulaNormalized.neg A :: Δ))

/-- Definition 3.6.1: Two-premise rules of LK' (and-right, or-left shared-
    context; impl-left split context; cut rule). -/
@[blueprint "chap3__definition_3_6_1" (main := true)]
inductive LKStep2 : Sequent → Sequent → Sequent → Type where
  | andRight (Γ Δ : List PropFormulaNormalized) (A B : PropFormulaNormalized) :
      LKStep2 (Sequent.mk Γ (A :: Δ))
              (Sequent.mk Γ (B :: Δ))
              (Sequent.mk Γ (PropFormulaNormalized.conj A B :: Δ))
  | orLeft (Γ Δ : List PropFormulaNormalized) (A B : PropFormulaNormalized) :
      LKStep2 (Sequent.mk (A :: Γ) Δ)
              (Sequent.mk (B :: Γ) Δ)
              (Sequent.mk (PropFormulaNormalized.disj A B :: Γ) Δ)
  | implLeft (Γ Δ Λ Θ : List PropFormulaNormalized) (A B : PropFormulaNormalized) :
      LKStep2 (Sequent.mk Γ (A :: Δ))
              (Sequent.mk (B :: Λ) Θ)
              (Sequent.mk (PropFormulaNormalized.impl A B :: Γ ++ Λ) (Δ ++ Θ))
  | cut (Γ Δ Λ Θ : List PropFormulaNormalized) (A : PropFormulaNormalized) :
      LKStep2 (Sequent.mk Γ (A :: Δ))
              (Sequent.mk (A :: Λ) Θ)
              (Sequent.mk (Γ ++ Λ) (Δ ++ Θ))

-- ========= Definition 3.6.1: LK' Axioms =========

/-- Definition 3.6.1: A sequent is an LK' axiom iff it has the form
    [A] → [A] (antecedent and succedent singletons containing the same A). -/
@[blueprint "chap3__definition_3_6_1" (main := true)]
def isLKAxiom (s : Sequent) : Prop :=
  ∃ A : PropFormulaNormalized, s.antecedent = [A] ∧ s.succedent = [A]

-- ========= Definition 3.6.1: LK' Proof Tree (indexed) =========

/-- Definition 3.6.1: LK' proof trees indexed by their conclusion sequent,
    with axiom leaves and closed under one-premise and two-premise LK' rules. -/
@[blueprint "chap3__definition_3_6_1" (main := true)]
inductive LKProofTree : Sequent → Type where
  | axiom_ (A : PropFormulaNormalized) : LKProofTree (Sequent.mk [A] [A])
  | onePremise {prem conc : Sequent}
      (rule : LKStep1 prem conc) (t : LKProofTree prem) : LKProofTree conc
  | twoPremise {prem1 prem2 conc : Sequent}
      (rule : LKStep2 prem1 prem2 conc)
      (t1 : LKProofTree prem1) (t2 : LKProofTree prem2) : LKProofTree conc

-- ========= Definition 3.6.1 (companion defs): Cut-free =========

namespace LKStep2

/-- Definition 3.6.1 (companion): A two-premise step is cut-free iff it is not
    the cut constructor. -/
@[blueprint "chap3__definition_3_6_1"]
def isCutFree {prem1 prem2 conc : Sequent}
    (rule : LKStep2 prem1 prem2 conc) : Prop :=
  match rule with
  | .cut _ _ _ _ _ => False
  | .andRight _ _ _ _ => True
  | .orLeft _ _ _ _ => True
  | .implLeft _ _ _ _ _ _ => True

end LKStep2

namespace LKProofTree

/-- Definition 3.6.1 (companion): An LK' proof tree is cut-free iff every
    two-premise rule in the tree satisfies isCutFree (one-premise rules are
    always cut-free). -/
@[blueprint "chap3__definition_3_6_1"]
def isCutFree : {s : Sequent} → LKProofTree s → Prop
  | _, .axiom_ _ => True
  | _, .onePremise _ t => t.isCutFree
  | _, .twoPremise rule t1 t2 => rule.isCutFree ∧ t1.isCutFree ∧ t2.isCutFree

end LKProofTree

-- ========= Definition 3.6.1 (companion): LK'-provable =========

/-- Definition 3.6.1 (companion): A sequent is LK'-provable if there exists an
    LK' proof tree whose conclusion is that sequent. -/
@[blueprint "chap3__definition_3_6_1"]
def lkProvable (s : Sequent) : Prop :=
  Nonempty (LKProofTree s)

/-- Definition 3.6.1 (companion): A sequent is LK'-{cut}-provable if there
    exists a cut-free LK' proof tree whose conclusion is that sequent. -/
@[blueprint "chap3__definition_3_6_1"]
def lkCutFreeProvable (s : Sequent) : Prop :=
  ∃ (t : LKProofTree s), t.isCutFree

-- ========= Lemma 3.6.1: Soundness of LK' =========

/-- Lemma 3.6.1 (companion): Every LK' axiom is valid. An LK' axiom has the
    form [A] => [A], so for any valuation v, if v(A) = T then A is in the
    succedent and is true. -/
@[blueprint "chap3__lemma_3_6_1"]
theorem lkAxiom_valid (A : PropFormulaNormalized) :
    sequentValid (Sequent.mk [A] [A]) 

/-- Truth of a finite sequent under a fixed valuation. -/
@[blueprint "chap3__lemma_3_6_1"]
def lkSequentTrue (v : Valuation) (s : Sequent) : Prop :=
  (∀ A ∈ s.antecedent, evalExtN v A = BoolVal.T) →
    ∃ B ∈ s.succedent, evalExtN v B = BoolVal.T

/-- Lemma 3.6.1 (companion): Each one-premise LK' step preserves truth under a fixed valuation. -/
@[blueprint "chap3__lemma_3_6_1"]
theorem lkStep1_sound {prem conc : Sequent} (rule : LKStep1 prem conc)
    (v : Valuation) (hprem : lkSequentTrue v prem) : lkSequentTrue v conc 

/-- Lemma 3.6.1 (companion): Each two-premise LK' step preserves truth under a fixed valuation. -/
@[blueprint "chap3__lemma_3_6_1"]
theorem lkStep2_sound {prem1 prem2 conc : Sequent}
    (rule : LKStep2 prem1 prem2 conc)
    (v : Valuation) (hp1 : lkSequentTrue v prem1) (hp2 : lkSequentTrue v prem2) :
    lkSequentTrue v conc 

/-- Lemma 3.6.1 (companion): Soundness by induction on indexed LKProofTree. -/
@[blueprint "chap3__lemma_3_6_1"]
theorem lkProofTree_valid : {s : Sequent} → LKProofTree s → sequentValid s
-- BEGIN PROOF
  

/-- Lemma 3.6.1 (companion): Soundness of LK'. Every LK'-provable sequent
    is valid. For all sequents s, if there exists an LKProofTree s,
    then sequentValid s. Proved by structural induction on LKProofTree:
    base case uses lkAxiom_valid, inductive step uses lkStep1_sound
    and lkStep2_sound. -/
@[blueprint "chap3__lemma_3_6_1"]
theorem soundness_LK (s : Sequent) (h : lkProvable s) : sequentValid s 

/-- Lemma 3.6.1 (bundled): Soundness of LK'.
    (1) Every axiom of LK' is valid.
    (2) For every valuation, truth of the premises of each rule implies
        truth of its conclusion under that same valuation.
    (3) Every LK'-provable sequent is valid. -/
@[blueprint "chap3__lemma_3_6_1" (main := true)]
theorem lemma_3_6_1 :
    (∀ s, isLKAxiom s → sequentValid s) ∧
    (∀ {prem conc}, (rule : LKStep1 prem conc) →
      ∀ v, lkSequentTrue v prem → lkSequentTrue v conc) ∧
    (∀ {prem1 prem2 conc}, (rule : LKStep2 prem1 prem2 conc) →
      ∀ v, lkSequentTrue v prem1 → lkSequentTrue v prem2 → lkSequentTrue v conc) ∧
    (∀ s, lkProvable s → sequentValid s) 

-- ========= Theorem 3.6.1 (companion defs): Conversion Algorithms =========

/-- All-axiom leaves give the recursive proof predicate. -/
@[blueprint "chap3__theorem_3_6_1"]
theorem deductionTree_isProof_of_leaves : {s : Sequent} →
    (dt : DeductionTree s) → isProofTree dt → dt.isProof
  

/-- Theorem 3.6.1: Run search on the conclusion of an LK' proof and
    extract the resulting G' proof. Soundness certifies that search closes. -/
@[blueprint "chap3__theorem_3_6_1"]
def lkProof_to_gprimeProof {s : Sequent} (t : LKProofTree s) : ProofTree s :=
  (searchStart .systematic s).toProofTree (deductionTree_isProof_of_leaves _
    ((search_theorem_3_4_1 s).2.1 (lkProofTree_valid t)))

-- CutFreeTree: a bundled cut-free LK' proof tree.
@[blueprint "chap3__definition_3_6_1"]
abbrev CutFreeTree (s : Sequent) := { t : LKProofTree s // t.isCutFree }

-- isCutFree is invariant under Eq transport of the sequent index.
@[blueprint "chap3__theorem_3_6_1"]
theorem isCutFree_of_eq {s s' : Sequent} (h : s = s')
    (t : LKProofTree s) (hcf : t.isCutFree) :
    (h ▸ t).isCutFree 

-- Bundled transport for CutFreeTree.
@[blueprint "chap3__theorem_3_6_1"]
def cfCast {s s' : Sequent} (h : s = s') (ct : CutFreeTree s) :
    CutFreeTree s' :=
-- BEGIN PROOF
  ⟨h ▸ ct.val, isCutFree_of_eq h ct.val ct.property⟩

-- Bundled onePremise for CutFreeTree.
-- isCutFree (.onePremise rule t) = t.isCutFree definitionally.
@[blueprint "chap3__theorem_3_6_1"]
def cfOnePremise {prem conc : Sequent}
    (rule : LKStep1 prem conc) (ct : CutFreeTree prem) :
    CutFreeTree conc :=
  ⟨LKProofTree.onePremise rule ct.val, ct.property⟩

-- Bundled twoPremise for CutFreeTree (non-cut rules only).
@[blueprint "chap3__theorem_3_6_1"]
def cfAndRight {Γ Δ : List PropFormulaNormalized} {A B : PropFormulaNormalized}
    (ct1 : CutFreeTree (Sequent.mk Γ (A :: Δ)))
    (ct2 : CutFreeTree (Sequent.mk Γ (B :: Δ))) :
    CutFreeTree (Sequent.mk Γ (PropFormulaNormalized.conj A B :: Δ)) :=
  ⟨LKProofTree.twoPremise (LKStep2.andRight Γ Δ A B) ct1.val ct2.val,
   ⟨trivial, ct1.property, ct2.property⟩⟩

@[blueprint "chap3__theorem_3_6_1"]
def cfOrLeft {Γ Δ : List PropFormulaNormalized} {A B : PropFormulaNormalized}
    (ct1 : CutFreeTree (Sequent.mk (A :: Γ) Δ))
    (ct2 : CutFreeTree (Sequent.mk (B :: Γ) Δ)) :
    CutFreeTree (Sequent.mk (PropFormulaNormalized.disj A B :: Γ) Δ) :=
  ⟨LKProofTree.twoPremise (LKStep2.orLeft Γ Δ A B) ct1.val ct2.val,
   ⟨trivial, ct1.property, ct2.property⟩⟩

@[blueprint "chap3__theorem_3_6_1"]
def cfImplLeft {Γ Δ Λ Θ : List PropFormulaNormalized} {A B : PropFormulaNormalized}
    (ct1 : CutFreeTree (Sequent.mk Γ (A :: Δ)))
    (ct2 : CutFreeTree (Sequent.mk (B :: Λ) Θ)) :
    CutFreeTree (Sequent.mk (PropFormulaNormalized.impl A B :: Γ ++ Λ) (Δ ++ Θ)) :=
  ⟨LKProofTree.twoPremise (LKStep2.implLeft Γ Δ Λ Θ A B) ct1.val ct2.val,
   ⟨trivial, ct1.property, ct2.property⟩⟩

-- Bundled axiom.
@[blueprint "chap3__theorem_3_6_1"]
def cfAxiom (A : PropFormulaNormalized) :
    CutFreeTree (Sequent.mk [A] [A]) :=
  ⟨LKProofTree.axiom_ A, trivial⟩

-- Bundled structural helpers built from cfOnePremise and cfCast.
@[blueprint "chap3__theorem_3_6_1"]
def cfSinkLeftPast : (before middle after : List PropFormulaNormalized) →
    (Δ : List PropFormulaNormalized) → (A : PropFormulaNormalized) →
    CutFreeTree (Sequent.mk (before ++ [A] ++ middle ++ after) Δ) →
    CutFreeTree (Sequent.mk (before ++ middle ++ [A] ++ after) Δ)
  | _, [], _, _, _, ct => cfCast (by simp) ct
  | before, B :: rest, after, Δ, A, ct =>
    let ct1 := cfCast (by simp) ct
    let ct2 := cfOnePremise (LKStep1.exchangeLeft before (rest ++ after) Δ A B) ct1
    let ct3 := cfCast (by simp) ct2
    let ct4 := cfSinkLeftPast (before ++ [B]) rest after Δ A ct3
    cfCast (by simp) ct4

@[blueprint "chap3__theorem_3_6_1"]
def cfSinkRightPast : (before middle after : List PropFormulaNormalized) →
    (Γ : List PropFormulaNormalized) → (A : PropFormulaNormalized) →
    CutFreeTree (Sequent.mk Γ (before ++ [A] ++ middle ++ after)) →
    CutFreeTree (Sequent.mk Γ (before ++ middle ++ [A] ++ after))
  | _, [], _, _, _, ct => cfCast (by simp) ct
  | before, B :: rest, after, Γ, A, ct =>
    let ct1 := cfCast (by simp) ct
    let ct2 := cfOnePremise (LKStep1.exchangeRight Γ before (rest ++ after) A B) ct1
    let ct3 := cfCast (by simp) ct2
    let ct4 := cfSinkRightPast (before ++ [B]) rest after Γ A ct3
    cfCast (by simp) ct4

@[blueprint "chap3__theorem_3_6_1"]
def cfFloatLeftPast : (before middle after : List PropFormulaNormalized) →
    (Δ : List PropFormulaNormalized) → (A : PropFormulaNormalized) →
    CutFreeTree (Sequent.mk (before ++ middle ++ [A] ++ after) Δ) →
    CutFreeTree (Sequent.mk (before ++ [A] ++ middle ++ after) Δ)
  | _, [], _, _, _, ct => cfCast (by simp) ct
  | before, B :: rest, after, Δ, A, ct =>
    let ct0 := cfFloatLeftPast (before ++ [B]) rest after Δ A (cfCast (by simp) ct)
    let ct1 := cfCast (by simp) ct0
    let ct2 := cfOnePremise (LKStep1.exchangeLeft before (rest ++ after) Δ B A) ct1
    cfCast (by simp) ct2

@[blueprint "chap3__theorem_3_6_1"]
def cfFloatRightPast : (before middle after : List PropFormulaNormalized) →
    (Γ : List PropFormulaNormalized) → (A : PropFormulaNormalized) →
    CutFreeTree (Sequent.mk Γ (before ++ middle ++ [A] ++ after)) →
    CutFreeTree (Sequent.mk Γ (before ++ [A] ++ middle ++ after))
  | _, [], _, _, _, ct => cfCast (by simp) ct
  | before, B :: rest, after, Γ, A, ct =>
    let ct0 := cfFloatRightPast (before ++ [B]) rest after Γ A (cfCast (by simp) ct)
    let ct1 := cfCast (by simp) ct0
    let ct2 := cfOnePremise (LKStep1.exchangeRight Γ before (rest ++ after) B A) ct1
    cfCast (by simp) ct2

@[blueprint "chap3__theorem_3_6_1"]
def cfWeakenLeftPrepend : (Γ' : List PropFormulaNormalized) →
    {Γ Δ : List PropFormulaNormalized} →
    CutFreeTree (Sequent.mk Γ Δ) →
    CutFreeTree (Sequent.mk (Γ' ++ Γ) Δ)
  | [], _, _, ct => ct
  | A :: rest, Γ, Δ, ct =>
    cfOnePremise (LKStep1.weakenLeft (rest ++ Γ) Δ A) (cfWeakenLeftPrepend rest ct)

@[blueprint "chap3__theorem_3_6_1"]
def cfWeakenRightPrepend : (Δ' : List PropFormulaNormalized) →
    {Γ Δ : List PropFormulaNormalized} →
    CutFreeTree (Sequent.mk Γ Δ) →
    CutFreeTree (Sequent.mk Γ (Δ' ++ Δ))
  | [], _, _, ct => ct
  | A :: rest, Γ, Δ, ct =>
    cfOnePremise (LKStep1.weakenRight Γ (rest ++ Δ) A) (cfWeakenRightPrepend rest ct)

@[blueprint "chap3__theorem_3_6_1"]
def cfWeakenLeftAppend : (Γ' : List PropFormulaNormalized) →
    {Γ Δ : List PropFormulaNormalized} →
    CutFreeTree (Sequent.mk Γ Δ) →
    CutFreeTree (Sequent.mk (Γ ++ Γ') Δ)
  | [], _, _, ct => cfCast (by simp) ct
  | A :: rest, Γ, Δ, ct =>
    let ct1 := cfWeakenLeftAppend rest ct
    let ct2 := cfOnePremise (LKStep1.weakenLeft (Γ ++ rest) Δ A) ct1
    let ct3 : CutFreeTree (Sequent.mk ([] ++ [A] ++ Γ ++ rest) Δ) := cfCast (by simp) ct2
    let ct4 := cfSinkLeftPast [] Γ rest Δ A ct3
    cfCast (by simp) ct4

@[blueprint "chap3__theorem_3_6_1"]
def cfWeakenRightAppend : (Δ' : List PropFormulaNormalized) →
    {Γ Δ : List PropFormulaNormalized} →
    CutFreeTree (Sequent.mk Γ Δ) →
    CutFreeTree (Sequent.mk Γ (Δ ++ Δ'))
  | [], _, _, ct => cfCast (by simp) ct
  | A :: rest, Γ, Δ, ct =>
    let ct1 := cfWeakenRightAppend rest ct
    let ct2 := cfOnePremise (LKStep1.weakenRight Γ (Δ ++ rest) A) ct1
    let ct3 : CutFreeTree (Sequent.mk Γ ([] ++ [A] ++ Δ ++ rest)) := cfCast (by simp) ct2
    let ct4 := cfSinkRightPast [] Δ rest Γ A ct3
    cfCast (by simp) ct4

@[blueprint "chap3__theorem_3_6_1"]
def cfContractDupLeft (pfx : List PropFormulaNormalized) :
    (L : List PropFormulaNormalized) → (Δ : List PropFormulaNormalized) →
    CutFreeTree (Sequent.mk (pfx ++ L ++ L) Δ) →
    CutFreeTree (Sequent.mk (pfx ++ L) Δ)
  | [], _, ct => cfCast (by simp) ct
  | A :: rest, Δ, ct =>
    have h0 : Sequent.mk (pfx ++ (A :: rest) ++ (A :: rest)) Δ =
              Sequent.mk (pfx ++ [A] ++ rest ++ ([A] ++ rest)) Δ := by simp
    let ct0 := cfSinkLeftPast pfx rest ([A] ++ rest) Δ A (cfCast h0 ct)
    have ha : Sequent.mk (pfx ++ rest ++ [A] ++ ([A] ++ rest)) Δ =
              Sequent.mk ((pfx ++ rest) ++ (A :: A :: rest)) Δ := by simp
    let ct1 := cfOnePremise
      (LKStep1.contractLeft (pfx ++ rest) rest Δ A) (cfCast ha ct0)
    have hb : Sequent.mk ((pfx ++ rest) ++ (A :: rest)) Δ =
              Sequent.mk (pfx ++ rest ++ [A] ++ rest) Δ := by simp
    let ct2 := cfFloatLeftPast pfx rest rest Δ A (cfCast hb ct1)
    have hc : Sequent.mk (pfx ++ [A] ++ rest ++ rest) Δ =
              Sequent.mk ((pfx ++ [A]) ++ rest ++ rest) Δ := by simp
    have hd : Sequent.mk ((pfx ++ [A]) ++ rest) Δ =
              Sequent.mk (pfx ++ (A :: rest)) Δ := by simp
    cfCast hd (cfContractDupLeft (pfx ++ [A]) rest Δ (cfCast hc ct2))

@[blueprint "chap3__theorem_3_6_1"]
def cfContractDupRight (pfx : List PropFormulaNormalized) :
    (L : List PropFormulaNormalized) → (Γ : List PropFormulaNormalized) →
    CutFreeTree (Sequent.mk Γ (pfx ++ L ++ L)) →
    CutFreeTree (Sequent.mk Γ (pfx ++ L))
  | [], _, ct => cfCast (by simp) ct
  | A :: rest, Γ, ct =>
    have h0 : Sequent.mk Γ (pfx ++ (A :: rest) ++ (A :: rest)) =
              Sequent.mk Γ (pfx ++ [A] ++ rest ++ ([A] ++ rest)) := by simp
    let ct0 := cfSinkRightPast pfx rest ([A] ++ rest) Γ A (cfCast h0 ct)
    have ha : Sequent.mk Γ (pfx ++ rest ++ [A] ++ ([A] ++ rest)) =
              Sequent.mk Γ ((pfx ++ rest) ++ (A :: A :: rest)) := by simp
    let ct1 := cfOnePremise
      (LKStep1.contractRight Γ (pfx ++ rest) rest A) (cfCast ha ct0)
    have hb : Sequent.mk Γ ((pfx ++ rest) ++ (A :: rest)) =
              Sequent.mk Γ (pfx ++ rest ++ [A] ++ rest) := by simp
    let ct2 := cfFloatRightPast pfx rest rest Γ A (cfCast hb ct1)
    have hc : Sequent.mk Γ (pfx ++ [A] ++ rest ++ rest) =
              Sequent.mk Γ ((pfx ++ [A]) ++ rest ++ rest) := by simp
    have hd : Sequent.mk Γ ((pfx ++ [A]) ++ rest) =
              Sequent.mk Γ (pfx ++ (A :: rest)) := by simp
    cfCast hd (cfContractDupRight (pfx ++ [A]) rest Γ (cfCast hc ct2))

/-- Split a list at a known member by scanning the list. -/
@[blueprint "chap3__theorem_3_6_1"]
def splitAtMember (A : PropFormulaNormalized) :
    (L : List PropFormulaNormalized) → A ∈ L →
    { parts : List PropFormulaNormalized × List PropFormulaNormalized //
      L = parts.1 ++ [A] ++ parts.2 }
  | [], h => False.elim (List.not_mem_nil h)
  | B :: rest, h =>
    if heq : A = B then ⟨([], rest), by simp [heq]⟩
    else
      let parts := splitAtMember A rest ((List.mem_cons.mp h).resolve_left heq)
      ⟨(B :: parts.val.1, parts.val.2), by simpa using congrArg (B :: ·) parts.property⟩

/-- Build a cut-free axiom expansion using explicit finite-list scans. -/
@[blueprint "chap3__theorem_3_6_1"]
def cfProofOfShared
    (Γ Δ : List PropFormulaNormalized) (A : PropFormulaNormalized)
    (hΓ : A ∈ Γ) (hΔ : A ∈ Δ) : CutFreeTree (Sequent.mk Γ Δ) :=
  let left := splitAtMember A Γ hΓ
  let right := splitAtMember A Δ hΔ
  cfCast ((congrArg (fun Γ => Sequent.mk Γ (right.val.1 ++ [A] ++ right.val.2))
      left.property.symm).trans (congrArg (Sequent.mk Γ) right.property.symm))
    (cfWeakenRightAppend right.val.2 (cfWeakenRightPrepend right.val.1
      (cfWeakenLeftAppend left.val.2 (cfWeakenLeftPrepend left.val.1 (cfAxiom A)))))

/-- Locate a common formula in an axiom by scanning its antecedent. -/
@[blueprint "chap3__theorem_3_6_1"]
def sharedAxiomFormula (Γ Δ : List PropFormulaNormalized)
    (h : ∃ A, A ∈ Γ ∧ A ∈ Δ) : { A // A ∈ Γ ∧ A ∈ Δ } :=
  match Γ with
  | [] => False.elim (by obtain ⟨A, ha, _⟩ := h; exact List.not_mem_nil ha)
  | A :: rest =>
    if ha : A ∈ Δ then ⟨A, List.Mem.head _, ha⟩
    else
      let found := sharedAxiomFormula rest Δ (by
        obtain ⟨B, hb, hd⟩ := h
        exact ⟨B, (List.mem_cons.mp hb).resolve_left (fun heq => ha (heq ▸ hd)), hd⟩)
      ⟨found.val, List.Mem.tail _ found.property.1, found.property.2⟩

-- Conversion of G' proof trees to cut-free LK' proof trees.
-- Each G' rule is simulated by a sequence of cut-free LK' rules.

-- Convert a G' proof tree to a cut-free LK' proof tree by structural recursion.
@[blueprint "chap3__theorem_3_6_1"]
def gProofToLKCutFree :
    {s : Sequent} → ProofTree s → CutFreeTree s
  | _, .axiom_ s h =>
    let found := sharedAxiomFormula s.antecedent s.succedent h
    cfProofOfShared s.antecedent s.succedent found.val found.property.1 found.property.2
  | _, .onePremise rule subtree => by
    let ct := gProofToLKCutFree subtree
    exact gStep1ToLK rule ct
  | _, .twoPremise rule t1 t2 => by
    let ct1 := gProofToLKCutFree t1
    let ct2 := gProofToLKCutFree t2
    exact gStep2ToLK rule ct1 ct2
where
  -- Simulate G' one-premise rules with cut-free LK' rules.
  gStep1ToLK : {prem conc : Sequent} → GentzenStep1 prem conc →
      CutFreeTree prem → CutFreeTree conc
    | _, _, .andLeft Γ Δ Λ A B, ct =>
      -- IH: ct is proof of Γ ++ [A, B] ++ Δ → Λ
      -- Goal: proof of Γ ++ [A∧B] ++ Δ → Λ
      let Γ' := Γ ++ [B] ++ Δ  -- rest after A
      -- Float A to pos 0
      let ct1 : CutFreeTree ⟨A :: Γ', Λ⟩ :=
        cfCast (by simp [Γ']) (cfFloatLeftPast [] Γ ([B] ++ Δ) Λ A (cfCast (by simp) ct))
      -- Apply andLeft1: A :: Γ' → (.conj A B) :: Γ'
      let ct2 := cfOnePremise (LKStep1.andLeft1 Γ' Λ A B) ct1
      -- Float B to pos 0 (B is somewhere inside Γ' = Γ ++ [B] ++ Δ)
      let ct3 : CutFreeTree ⟨B :: (.conj A B :: Γ ++ Δ), Λ⟩ :=
        cfCast (by simp) (cfFloatLeftPast [] ([.conj A B] ++ Γ) Δ Λ B
          (cfCast (by simp [Γ']) ct2))
      -- Apply andLeft2: B :: rest → (.conj A B) :: rest
      let ct4 := cfOnePremise (LKStep1.andLeft2 (.conj A B :: Γ ++ Δ) Λ A B) ct3
      -- Contract the two A∧B copies
      let ct5 := cfOnePremise (LKStep1.contractLeft [] (Γ ++ Δ) Λ (.conj A B)) ct4
      -- Sink A∧B back to position |Γ|
      cfSinkLeftPast [] Γ Δ Λ (.conj A B) (cfCast (by simp) ct5)
    | _, _, .orRight Γ Δ Λ A B, ct =>
      -- IH: ct is proof of Γ → Δ ++ [A, B] ++ Λ
      -- Goal: proof of Γ → Δ ++ [A∨B] ++ Λ
      let Δ' := Δ ++ [B] ++ Λ  -- rest after A
      let ct1 : CutFreeTree ⟨Γ, A :: Δ'⟩ :=
        cfCast (by simp [Δ']) (cfFloatRightPast [] Δ ([B] ++ Λ) Γ A (cfCast (by simp) ct))
      let ct2 := cfOnePremise (LKStep1.orRight1 Γ Δ' A B) ct1
      -- Float B to pos 0 (B is inside Δ' = Δ ++ [B] ++ Λ)
      let ct3 : CutFreeTree ⟨Γ, B :: (.disj A B :: Δ ++ Λ)⟩ :=
        cfCast (by simp) (cfFloatRightPast [] ([.disj A B] ++ Δ) Λ Γ B
          (cfCast (by simp [Δ']) ct2))
      let ct4 := cfOnePremise (LKStep1.orRight2 Γ (.disj A B :: Δ ++ Λ) A B) ct3
      let ct5 := cfOnePremise (LKStep1.contractRight Γ [] (Δ ++ Λ) (.disj A B)) ct4
      cfSinkRightPast [] Δ Λ Γ (.disj A B) (cfCast (by simp) ct5)
    | _, _, .implRight Γ Δ Λ A B, ct => by
      -- IH: ct is proof of A :: Γ → B :: (Δ ++ Λ)
      -- Goal: proof of Γ → Δ ++ [A→B] ++ Λ
      -- Apply implRight: from A :: Γ → B :: (Δ ++ Λ) derive Γ → (A→B) :: (Δ ++ Λ)
      let ct1 := cfOnePremise (LKStep1.implRight Γ (Δ ++ Λ) A B) ct
      -- Sink A→B back to position |Δ| in succedent
      exact cfCast (by simp) (cfSinkRightPast [] Δ Λ Γ (.impl A B) (cfCast (by simp) ct1))
    | _, _, .negLeft Γ Δ Λ A, ct => by
      -- IH: ct is proof of Γ ++ Δ → [A] ++ Λ
      -- Goal: proof of Γ ++ [¬A] ++ Δ → Λ
      -- LK' negLeft: from Γ' → A :: Δ' derive (¬A) :: Γ' → Δ'
      -- Apply negLeft with Γ' = Γ ++ Δ, Δ' = Λ:
      -- from Γ ++ Δ → A :: Λ derive (¬A) :: Γ ++ Δ → Λ
      let ct1 := cfOnePremise (LKStep1.negLeft (Γ ++ Δ) Λ A) ct
      -- Sink ¬A from pos 0 to pos |Γ|
      exact cfSinkLeftPast [] Γ Δ Λ (.neg A) (cfCast (by simp) ct1)
    | _, _, .negRight Γ Δ Λ A, ct => by
      -- IH: ct is proof of [A] ++ Γ → Δ ++ Λ
      -- Goal: proof of Γ → Δ ++ [¬A] ++ Λ
      -- LK' negRight: from A :: Γ' → Δ' derive Γ' → (¬A) :: Δ'
      -- Apply negRight with Γ' = Γ, Δ' = Δ ++ Λ:
      let ct1 := cfOnePremise (LKStep1.negRight Γ (Δ ++ Λ) A) ct
      -- Sink ¬A from pos 0 to pos |Δ| in succedent
      exact cfCast (by simp) (cfSinkRightPast [] Δ Λ Γ (.neg A) (cfCast (by simp) ct1))
  -- Simulate G' two-premise rules with cut-free LK' rules.
  gStep2ToLK : {p1 p2 conc : Sequent} → GentzenStep2 p1 p2 conc →
      CutFreeTree p1 → CutFreeTree p2 → CutFreeTree conc
    | _, _, _, .andRight Γ Δ Λ A B, ct1, ct2 => by
      -- ct1: Γ → Δ ++ [A] ++ Λ,  ct2: Γ → Δ ++ [B] ++ Λ
      -- Goal: Γ → Δ ++ [A∧B] ++ Λ
      -- Float A to pos 0 in ct1, B to pos 0 in ct2
      let c1 := cfFloatRightPast [] Δ Λ Γ A ct1
      let c2 := cfFloatRightPast [] Δ Λ Γ B ct2
      -- Apply andRight: from Γ → A :: (Δ++Λ) and Γ → B :: (Δ++Λ) derive Γ → (A∧B) :: (Δ++Λ)
      let ct3 := cfAndRight c1 c2
      -- Sink A∧B back to pos |Δ|
      exact cfCast (by simp) (cfSinkRightPast [] Δ Λ Γ (.conj A B) (cfCast (by simp) ct3))
    | _, _, _, .orLeft Γ Δ Λ A B, ct1, ct2 => by
      -- ct1: Γ ++ [A] ++ Δ → Λ,  ct2: Γ ++ [B] ++ Δ → Λ
      -- Goal: Γ ++ [A∨B] ++ Δ → Λ
      -- Float A to pos 0 in ct1, B to pos 0 in ct2
      let c1 := cfFloatLeftPast [] Γ Δ Λ A ct1
      let c2 := cfFloatLeftPast [] Γ Δ Λ B ct2
      -- Apply orLeft
      let ct3 := cfOrLeft c1 c2
      -- Sink A∨B back to pos |Γ|
      exact cfSinkLeftPast [] Γ Δ Λ (.disj A B) (cfCast (by simp) ct3)
    | _, _, _, .implLeft Γ Δ Λ A B, ct1, ct2 => by
      -- ct1: Γ ++ Δ → [A] ++ Λ,  ct2: [B] ++ Γ ++ Δ → Λ
      -- Goal: Γ ++ [A→B] ++ Δ → Λ
      -- LK' implLeft: from Γ' → A :: Δ' and B :: Λ' → Θ' derive (A→B) :: Γ'++Λ' → Δ'++Θ'
      -- Use Γ' = Γ++Δ, Δ' = Λ, Λ' = Γ++Δ, Θ' = Λ
      -- Then conclusion is (A→B) :: (Γ++Δ) ++ (Γ++Δ) → Λ ++ Λ
      let ct3 := cfImplLeft ct1 ct2
      -- Contract duplicated antecedent (Γ++Δ) and succedent (Λ)
      let ct4 := cfContractDupLeft [.impl A B] (Γ ++ Δ) (Λ ++ Λ)
        (cfCast (by simp) ct3)
      let ct5 := cfContractDupRight [] Λ ((PropFormulaNormalized.impl A B) :: Γ ++ Δ)
        (cfCast (by simp) ct4)
      -- Now we have (A→B) :: Γ ++ Δ → Λ
      -- Sink A→B from pos 0 to pos |Γ|
      exact cfSinkLeftPast [] Γ Δ Λ (.impl A B) (cfCast (by simp) ct5)

/-- Theorem 3.6.1 (companion): Completeness of cut-free LK'. Every valid
    finite sequent has a cut-free LK' proof tree: run G' search and
    structurally convert its certified result. -/
@[blueprint "chap3__theorem_3_6_1"]
def validSequent_to_cutFreeLKProof
    (s : Sequent) (hv : sequentValid s) :
    CutFreeTree s :=
  gProofToLKCutFree ((searchStart .systematic s).toProofTree
    (deductionTree_isProof_of_leaves _ ((search_theorem_3_4_1 s).2.1 hv)))

/-- Theorem 3.6.1 (companion): Convert a G'-proof to a cut-free LK'-proof
    by structural recursion on the supplied proof. -/
@[blueprint "chap3__theorem_3_6_1"]
def gprimeProof_to_cutFreeLKProof {s : Sequent}
    (t : ProofTree s) : LKProofTree s :=
  (gProofToLKCutFree t).val

-- Helper: gprimeProof_to_cutFreeLKProof produces cut-free trees.
@[blueprint "chap3__theorem_3_6_1"]
theorem gprimeProof_to_cutFreeLKProof_isCutFree
    {s : Sequent} (t : ProofTree s) :
    (gprimeProof_to_cutFreeLKProof t).isCutFree 

-- ========= Theorem 3.6.1: Logical Equivalence of G', LK', and LK'-{cut} =========

/-- Theorem 3.6.1: G', LK', and LK'-{cut} prove exactly the same sequents.
    Part (1): LK'-provable implies G'-provable (via lkProof_to_gprimeProof).
    Part (2): G'-provable implies LK'-{cut}-provable
    (via gprimeProof_to_cutFreeLKProof).
    The equivalence chain is: LK'-{cut} provable implies LK'-provable
    (trivially), LK'-provable implies G'-provable (part 1), G'-provable
    implies LK'-{cut}-provable (part 2). Semantic cut elimination follows
    as a corollary. -/
@[blueprint "chap3__theorem_3_6_1" (main := true)]
theorem lk_gprime_equivalence (s : Sequent) :
    (lkProvable s → sequentProvable s) ∧
    (sequentProvable s → lkCutFreeProvable s) 

-- ========= Lemma 3.6.2: Consistency for arbitrary sets =========

/-- A proof from a possibly infinite set has a finite list of assumptions. -/
@[blueprint "chap3__lemma_3_6_2"]
def lkSetProvable (Γ : Set PropFormulaNormalized) (A : PropFormulaNormalized) : Prop :=
  ∃ L : List PropFormulaNormalized, (∀ B ∈ L, B ∈ Γ) ∧ lkProvable ⟨L, [A]⟩

/-- Syntactic inconsistency means that every formula is provable. -/
@[blueprint "chap3__lemma_3_6_2"]
def lkInconsistent (Γ : Set PropFormulaNormalized) : Prop :=
  ∀ A, lkSetProvable Γ A

@[blueprint "chap3__lemma_3_6_2"]
def lkConsistent (Γ : Set PropFormulaNormalized) : Prop := ¬ lkInconsistent Γ

/-- Finite completeness of LK'. -/
@[blueprint "chap3__theorem_3_6_1"]
theorem valid_to_lkProvable (s : Sequent) (hv : sequentValid s) : lkProvable s 

/-- Contradictory finite proof witnesses imply every formula by negation,
    cut, and weakening, concatenating their finite antecedents. -/
@[blueprint "chap3__lemma_3_6_2"]
theorem lkSetProvable_contradiction {Γ : Set PropFormulaNormalized}
    {A : PropFormulaNormalized} (hA : lkSetProvable Γ A)
    (hnA : lkSetProvable Γ (.neg A)) : lkInconsistent Γ 

/-- Provability is monotone in its set of assumptions. -/
@[blueprint "chap3__lemma_3_6_2"]
theorem lkSetProvable_mono {Γ Δ : Set PropFormulaNormalized}
    (hsub : Γ ⊆ Δ) {A : PropFormulaNormalized} :
    lkSetProvable Γ A → lkSetProvable Δ A 

/-- A finite proof using ¬A as an extra assumption and concluding A
    yields a proof of A from a finite subset of the original set. -/
@[blueprint "chap3__lemma_3_6_2"]
theorem lkSetProvable_remove_neg {Γ : Set PropFormulaNormalized}
    {A : PropFormulaNormalized}
    (h : lkSetProvable (Γ ∪ Set.singleton (.neg A)) A) : lkSetProvable Γ A 

/-- Lemma 3.6.2: Both syntactic characterizations for arbitrary, possibly
    infinite sets. Every use of provability carries finite assumptions. -/
@[blueprint "chap3__lemma_3_6_2" (main := true)]
theorem consistency_characterization_LK (Γ : Set PropFormulaNormalized) :
    (lkInconsistent Γ ↔ ∃ A, lkSetProvable Γ A ∧ lkSetProvable Γ (.neg A)) ∧
    (∀ A, (¬ lkSetProvable Γ A ↔ lkConsistent (Γ ∪ Set.singleton (.neg A)))) 

end LCS.Propositional.LK
