import LCS.Herbrand.HerbrandTheorem.Main.Part2

section

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

proof_of herbrandExSigmaObservations := by
  -- REPAIR(T7-132): proof pending
  sorry


helper /-- Example 7.5.3: the third prefix restores the universal associated with
the first maximal term g(f(a)); its fresh name is u and the remaining terms
are a,f(a). This is the concrete first selection only. -/
theorem herbrandExFirstMaximalSelection :
    herbrandExProofReconstructionOrder.head? = herbrandExFreshTerm 7 ∧
    herbrandExFreshName (.func .g (fun _ => .func .f (fun _ => .const .a))) = some 7 ∧
    herbrandExTermSetHT.take 2 = [.const .a, .func .f (fun _ => .const .a)] := by
  exact ⟨rfl, rfl, rfl⟩

helper /-- Example 7.5.3: the last four prefixes retain their actual predecessor
subtrees, and the complete proof reaches the original H′ boundary at depth 19. -/
theorem herbrandExRemainingPrefixConnections :
    LCS.Herbrand.SharpenedHauptsatz.Permutability.lkSubtreeAt herbrandExPrefix4 [0,0,0] =
      some ⟨herbrandExReconstruction3, herbrandExPrefix3⟩ ∧
    LCS.Herbrand.SharpenedHauptsatz.Permutability.lkSubtreeAt herbrandExPrefix5 (List.replicate 5 0) =
      some ⟨herbrandExReconstruction4, herbrandExPrefix4⟩ ∧
    LCS.Herbrand.SharpenedHauptsatz.Permutability.lkSubtreeAt herbrandExPrefix6 (List.replicate 5 0) =
      some ⟨herbrandExReconstruction5, herbrandExPrefix5⟩ ∧
    LCS.Herbrand.SharpenedHauptsatz.Permutability.lkSubtreeAt herbrandExPrefix7 [0] =
      some ⟨herbrandExReconstruction6, herbrandExPrefix6⟩ ∧
    LCS.Herbrand.SharpenedHauptsatz.Permutability.lkSubtreeAt herbrandExPrefix7 (List.replicate 19 0) =
      some ⟨herbrandExHPrime, herbrandExHPrimeProof⟩ := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

proof_of herbrandExSuffixRenamed := by
  -- REPAIR(T7-133): proof pending
  sorry


helper /-- CN26: an equality-free signature with one unary predicate P, no constants,
and no function symbols. In particular, there are no nullary functions. -/
def constantFreeExampleLanguage : Language where
  constSymbols := Empty
  funSymbols := Empty
  funArity := Empty.elim
  predSymbols := Unit
  predArity := fun _ => 1
  hasEquality := false

helper /-- CN26's unary atom P(t). -/
def constantFreeExampleP (t : Term constantFreeExampleLanguage) :
    FormulaN constantFreeExampleLanguage := .predN () (fun _ => t)

helper /-- CN26's sentence ∃x∃y(P(x) ∨ ¬P(y)), with x=0 and y=1. -/
def constantFreeExampleSentence : FormulaN constantFreeExampleLanguage :=
  .ex 0 (.ex 1 (.disj (constantFreeExampleP (.var 0))
    (.neg (constantFreeExampleP (.var 1)))))

helper /-- CN26's displayed midsequent → P(x) ∨ ¬P(x). -/
def constantFreeExampleMidsequent : Sequent constantFreeExampleLanguage :=
  ⟨[], [.disj (constantFreeExampleP (.var 0))
    (.neg (constantFreeExampleP (.var 0))) ]⟩

helper /-- CN26: the propositional upper proof of the displayed midsequent. -/
def constantFreeExampleUpperProof : FOLKProofTree constantFreeExampleMidsequent :=
  let A := constantFreeExampleP (.var 0)
  .onePremise (.contractRight (.disj A (.neg A)) [] [])
    (.onePremise (.orRightL A (.neg A) [] [.disj A (.neg A)])
      (.onePremise (.exchangeRight [] [] A (.disj A (.neg A)) [])
        (.onePremise (.orRightR A (.neg A) [] [A])
          (.onePremise (.negRight A [] [A])
            (.axiom_ ⟨[A], [A]⟩ ⟨A, rfl, rfl⟩)))))

helper /-- CN26: introduce ∃y with witness x at the displayed midsequent. -/
def constantFreeExampleFirstPrefix : FOLKProofTree (Sequent.mk []
    [.ex 1 (.disj (constantFreeExampleP (.var 0))
      (.neg (constantFreeExampleP (.var 1))))]) :=
  .onePremise (.exRight (.var 0) 1
    (.disj (constantFreeExampleP (.var 0)) (.neg (constantFreeExampleP (.var 1))))
    [] [] (by trivial)) constantFreeExampleUpperProof

helper /-- CN26: the actual proof of → ∃x∃y(P(x) ∨ ¬P(y)), obtained from the
stored midsequent by two existential-right inferences, both with witness x. -/
def constantFreeExampleProof :
    FOLKProofTree (Sequent.mk [] [constantFreeExampleSentence]) :=
  .onePremise (.exRight (.var 0) 0
    (.ex 1 (.disj (constantFreeExampleP (.var 0))
      (.neg (constantFreeExampleP (.var 1))))) [] []
    (by simp [isFreeForN, constantFreeExampleP, termFV,
      Membership.mem, Set.singleton])) constantFreeExampleFirstPrefix

helper /-- CN26: the stored upper proof is the node two unary edges above the
conclusion, not merely a separately provable sequent. -/
theorem constantFreeExampleMidsequentNode :
    LCS.Herbrand.SharpenedHauptsatz.Permutability.lkSubtreeAt
      constantFreeExampleProof [0, 0] =
      some ⟨constantFreeExampleMidsequent, constantFreeExampleUpperProof⟩ := by
  rfl

helper /-- CN26: the selected node satisfies both phases of the midsequent definition,
and the full concrete proof is cut-free. -/
theorem constantFreeExampleMidsequentCertificate :
    IsMidsequent constantFreeExampleProof constantFreeExampleMidsequent ∧
    constantFreeExampleProof.isCutFree := by
  constructor
  · refine ⟨?_, ⟨[0, 0], constantFreeExampleUpperProof,
      constantFreeExampleMidsequentNode, ?_, ?_⟩⟩
    · simp [constantFreeExampleMidsequent, constantFreeExampleP,
        FirstOrder.SemanticsN.isQuantifierFree]
    · exact ⟨Or.inl trivial, Or.inr ⟨trivial, id⟩, Or.inl trivial,
        Or.inr ⟨trivial, id⟩, Or.inr ⟨trivial, id⟩, trivial⟩
    · exact ⟨Or.inl trivial, id, Or.inl trivial, id, rfl⟩
  · trivial

helper /-- CN26: every term in this same signature is a variable, hence no ground
term exists. This uses the empty function alphabet as well as empty constants. -/
theorem constantFreeExampleNoGroundTerm (t : Term constantFreeExampleLanguage) :
    ¬ IsGroundTerm t := by
  cases t with
  | var _ => exact id
  | const c => exact Empty.elim c
  | func f _ => exact Empty.elim f

helper /-- CN26: no substitution of the displayed matrix is ground over the original
signature. Groundness is asserted of the resulting formula itself; no support
restriction or validity hypothesis is needed for this stronger impossibility. -/
theorem constantFreeExampleNoGroundInstance (sigma : _root_.LCS.Herbrand.HerbrandTheorem.Substitution constantFreeExampleLanguage) :
    formulaFVN (Substitution.applyFormula sigma
      (.disj (constantFreeExampleP (.var 0)) (.neg (constantFreeExampleP (.var 0))))) ≠ ∅ := by
  cases h : sigma 0 with
  | var n =>
    intro he
    have hn : n ∈ formulaFVN (Substitution.applyFormula sigma
        (.disj (constantFreeExampleP (.var 0)) (.neg (constantFreeExampleP (.var 0))))) := by
      exact Or.inl ⟨⟨0, by decide⟩, by simp [Substitution.applyTerm, h, termFV, Set.singleton]⟩
    rw [he] at hn
    exact hn
  | const c => exact Empty.elim c
  | func f _ => exact Empty.elim f

helper /-- CN26's negative assertion including validity: there is no valid ground
substitution instance of P(x) ∨ ¬P(x) in the constant-free signature. -/
theorem constantFreeExampleNoValidGroundInstance :
    ¬ ∃ sigma : _root_.LCS.Herbrand.HerbrandTheorem.Substitution constantFreeExampleLanguage,
      let D := Substitution.applyFormula sigma
        (.disj (constantFreeExampleP (.var 0)) (.neg (constantFreeExampleP (.var 0))))
      formulaFVN D = ∅ ∧ universallyValidN D := by
  rintro ⟨sigma, h, _⟩
  exact constantFreeExampleNoGroundInstance sigma h

helper /-- SQ039's separate repair: preserve P and the empty function alphabet,
and adjoin exactly one new constant # to the CN26 signature. -/
def constantFreeExampleCompletedLanguage : Language :=
  extendedLanguage constantFreeExampleLanguage Unit

helper /-- The ground instance P(#) ∨ ¬P(#) in the explicitly extended signature. -/
def constantFreeExampleCompletedInstance : FormulaN constantFreeExampleCompletedLanguage :=
  let P : FormulaN constantFreeExampleCompletedLanguage :=
    .predN () (fun _ => .const (.inr ()))
  .disj P (.neg P)

helper /-- SQ039: a concrete propositional proof of the ground instance after adjoining #. -/
def constantFreeExampleCompletedProof :
    FOLKProofTree (Sequent.mk [] [constantFreeExampleCompletedInstance]) :=
  let A : FormulaN constantFreeExampleCompletedLanguage :=
    .predN () (fun _ => .const (.inr ()))
  .onePremise (.contractRight (.disj A (.neg A)) [] [])
    (.onePremise (.orRightL A (.neg A) [] [.disj A (.neg A)])
      (.onePremise (.exchangeRight [] [] A (.disj A (.neg A)) [])
        (.onePremise (.orRightR A (.neg A) [] [A])
          (.onePremise (.negRight A [] [A])
            (.axiom_ ⟨[A], [A]⟩ ⟨A, rfl, rfl⟩)))))

helper /-- The adjoined constant supplies a ground, valid instance of the embedded
CN26 midsequent. This is a statement over the extension, separate from CN26's
impossibility over its original signature. -/
theorem constantFreeExampleAdjoinedRepair :
    IsGroundTerm (L := constantFreeExampleCompletedLanguage) (.const (.inr ())) ∧
    Substitution.applyFormula (L := constantFreeExampleCompletedLanguage)
      (fun x => if x = 0 then .const (.inr ()) else .var x)
      (.disj (.predN () (L := constantFreeExampleCompletedLanguage) (fun _ => .var 0))
        (.neg (.predN () (fun _ => .var 0)))) = constantFreeExampleCompletedInstance ∧
    formulaFVN constantFreeExampleCompletedInstance = ∅ ∧
    universallyValidN constantFreeExampleCompletedInstance := by
  refine ⟨True.intro, rfl, ?_, ?_⟩
  · funext x
    apply propext
    simp [constantFreeExampleCompletedInstance, formulaFVN, termFV,
      Set.iUnion, Set.union, Set.empty]
  · intro M s
    exact Classical.em _

helper /-- Correctness contract for a supplied LK witness-and-proof extractor.
The input is an actual pure-variable proof, cut-free, together with
its midsequent. The allocation certifies the normalized source Γ. The extractor
returns a source-associated full-prefix tuple sequence and a proof of its exact
Herbrand disjunction in the constant-completed signature. Correctness requires
constructibility of that returned sequence and a propositional/structural upper
proof (with inessential cuts permitted). The effective extractor is deferred;
this predicate specifies its result and does not provide an implementation. -/
def herbrand_substitution_pairs_LK {L : Language}
    (_hL : L.withoutEquality)
    (Gamma : List (FormulaN L)) (sd : _root_.LCS.Herbrand.HerbrandTheorem.SkolemData L Gamma)
    (extract : (T : FOLKProofTree (Sequent.mk [] Gamma)) →
      T.isCutFree → LCS.Herbrand.SharpenedHauptsatz.IsPureVariableProofLK T →
      (mid : Sequent L) → IsMidsequent T mid →
      (sps : SubstitutionPairSeq Gamma) × FOLKProofTree (HerbrandDisjunction sd sps)) :
    Prop :=
  ∀ T hCut hPure mid hMid,
    let output := extract T hCut hPure mid hMid
    IsConstructibleFromFunctionalForm Gamma output.1 sd ∧
    AllRulesPropStructInessentialLK output.2

helper /-- The single canonical allocation used by the LK functional-form interface. -/
def herbrand_skolemDataPerFormula_LK {L : Language} (Gamma : List (FormulaN L))
    (hInput : _root_.LCS.Herbrand.HerbrandTheorem.HerbrandInputConvention Gamma)
    (hPrenex : ∀ A ∈ Gamma, isPrenex A) : _root_.LCS.Herbrand.HerbrandTheorem.SkolemData L Gamma :=
  _root_.LCS.Herbrand.HerbrandTheorem.mkSkolemData Gamma hInput hPrenex

helper /-- Canonical occurrence resolver into the extended function/constant families. -/
def herbrand_resolveSymbolPerFormula_LK {L : Language}
    {Gamma : List (FormulaN L)} (sd : _root_.LCS.Herbrand.HerbrandTheorem.SkolemData L Gamma) := sd.symbol

helper /-- The rank of a new function equals its source dependency count. -/
theorem herbrand_hArityAtPerFormula_LK {L : Language}
    {Gamma : List (FormulaN L)} (f : _root_.LCS.Herbrand.HerbrandTheorem.ValiditySkolemFunction Gamma) :
    (_root_.LCS.Herbrand.HerbrandTheorem.validitySkolemLanguage Gamma).funArity (.inr f) = f.val.dependencies.length := rfl

helper /-- The canonical resolver satisfies the indexed resolution specification. -/
theorem herbrand_hRWPerFormula_LK {L : Language}
    {Gamma : List (FormulaN L)} (sd : _root_.LCS.Herbrand.HerbrandTheorem.SkolemData L Gamma) :
    _root_.LCS.Herbrand.HerbrandTheorem.SkolemResolverWellFormed sd (herbrand_resolveSymbolPerFormula_LK sd) :=
  fun _ => rfl

proof_of herbrandTheorem_LK := ⟨herbrandTheorem_forward_LK hL Gamma hAllPrenex hAllSentences hAllRectified hDistinct,
   herbrandTheorem_converse_LK hL Gamma hAllPrenex hAllSentences hAllRectified hDistinct⟩


helper /-- Correctness contract for a supplied LKₑ witness-and-proof extractor.
The input is an actual pure-variable proof, without essential cuts, together with
its midsequent. The allocation certifies the normalized source Γ. The extractor
returns a source-associated full-prefix tuple sequence and a proof of its exact
Herbrand disjunction in the constant-completed signature. Correctness requires
constructibility of that returned sequence and a propositional/structural upper
proof (with inessential cuts permitted). The effective extractor is deferred;
this predicate specifies its result and does not provide an implementation. -/
def herbrand_substitution_pairs_LKe {L : Language}
    (_hL : L.hasEquality = true)
    (Gamma : List (FormulaN L)) (sd : _root_.LCS.Herbrand.HerbrandTheorem.SkolemData L Gamma)
    (extract : (T : LCS.CutElim.LKe.LKeProofTree (Sequent.mk [] Gamma)) →
      noEssentialCuts T → LCS.Herbrand.SharpenedHauptsatz.IsPureVariableProofLKe T →
      (mid : Sequent L) → IsMidsequentLKe T mid →
      (sps : SubstitutionPairSeq Gamma) × LCS.CutElim.LKe.LKeProofTree (HerbrandDisjunction sd sps)) :
    Prop :=
  ∀ T hCut hPure mid hMid,
    let output := extract T hCut hPure mid hMid
    IsConstructibleFromFunctionalForm Gamma output.1 sd ∧
    AllRulesPropStructInessentialLKe output.2

helper /-- The single canonical allocation used by the LKe functional-form interface. -/
def herbrand_skolemDataPerFormula_LKe {L : Language} (Gamma : List (FormulaN L))
    (hInput : _root_.LCS.Herbrand.HerbrandTheorem.HerbrandInputConvention Gamma)
    (hPrenex : ∀ A ∈ Gamma, isPrenex A) : _root_.LCS.Herbrand.HerbrandTheorem.SkolemData L Gamma :=
  _root_.LCS.Herbrand.HerbrandTheorem.mkSkolemData Gamma hInput hPrenex

helper /-- Canonical occurrence resolver into the extended function/constant families. -/
def herbrand_resolveSymbolPerFormula_LKe {L : Language}
    {Gamma : List (FormulaN L)} (sd : _root_.LCS.Herbrand.HerbrandTheorem.SkolemData L Gamma) := sd.symbol

helper /-- The rank of a new function equals its source dependency count. -/
theorem herbrand_hArityAtPerFormula_LKe {L : Language}
    {Gamma : List (FormulaN L)} (f : _root_.LCS.Herbrand.HerbrandTheorem.ValiditySkolemFunction Gamma) :
    (_root_.LCS.Herbrand.HerbrandTheorem.validitySkolemLanguage Gamma).funArity (.inr f) = f.val.dependencies.length := rfl

helper /-- The canonical resolver satisfies the indexed resolution specification. -/
theorem herbrand_hRWPerFormula_LKe {L : Language}
    {Gamma : List (FormulaN L)} (sd : _root_.LCS.Herbrand.HerbrandTheorem.SkolemData L Gamma) :
    _root_.LCS.Herbrand.HerbrandTheorem.SkolemResolverWellFormed sd (herbrand_resolveSymbolPerFormula_LKe sd) :=
  fun _ => rfl

proof_of herbrandTheorem_LKe := by
  -- REPAIR(T7-59): proof pending
  sorry


helper /-- Helper: P(a, f(a)) as a formula in the Herbrand example language. -/
def herbrandEx_Pa : FormulaN herbrandExLang :=
  FormulaN.predN HerbrandExPred.P
    (vec2 (Term.const HerbrandExConst.a)
          (Term.func HerbrandExFunc.f
            (fun _ => Term.const HerbrandExConst.a)))

helper /-- Helper: Q(f(a), g(f(a))) as a formula in the Herbrand example
    language. -/
def herbrandEx_Qf : FormulaN herbrandExLang :=
  FormulaN.predN HerbrandExPred.Q
    (vec2 (Term.func HerbrandExFunc.f
            (fun _ => Term.const HerbrandExConst.a))
          (Term.func HerbrandExFunc.g
            (fun _ => Term.func HerbrandExFunc.f
              (fun _ => Term.const HerbrandExConst.a))))

helper /-- Helper: LK proof tree for the Pa branch of the Herbrand
    disjunction. Proves [] -> [neg Pa, neg Qf, Pa] by:
    Axiom [Pa]->[Pa], negRight, weakenRight neg Qf, two
    exchanges. Indexed by its conclusion sequent. -/
def herbrandEx_t1 :
    FOLKProofTree
      (Sequent.mk ([] : List (FormulaN herbrandExLang))
        [FormulaN.neg herbrandEx_Pa, FormulaN.neg herbrandEx_Qf,
         herbrandEx_Pa]) :=
  let Pa := herbrandEx_Pa
  let negPa := FormulaN.neg Pa
  let negQf := FormulaN.neg herbrandEx_Qf
  -- Axiom: [Pa] -> [Pa]
  let ax : FOLKProofTree (Sequent.mk [Pa] [Pa]) :=
    FOLKProofTree.axiom_ (Sequent.mk [Pa] [Pa]) ⟨Pa, rfl, rfl⟩
  -- negRight Pa [] [Pa]: [Pa] -> [Pa] ==> [] -> [] ++ [Pa, negPa]
  let negRule : FOLKStep1
      (Sequent.mk (Pa :: []) [Pa])
      (Sequent.mk [] ([Pa] ++ [negPa])) :=
    FOLKStep1.negRight Pa [] [Pa]
  let neg : FOLKProofTree (Sequent.mk [] ([Pa] ++ [negPa])) :=
    FOLKProofTree.onePremise negRule ax
  -- weakenRight negQf [] [Pa, negPa]: [] -> [Pa, negPa] ==>
  -- [] -> [Pa, negPa] ++ [negQf]
  let wkRule : FOLKStep1
      (Sequent.mk [] [Pa, negPa])
      (Sequent.mk [] ([Pa, negPa] ++ [negQf])) :=
    FOLKStep1.weakenRight negQf [] [Pa, negPa]
  let wk : FOLKProofTree (Sequent.mk [] ([Pa, negPa] ++ [negQf])) :=
    FOLKProofTree.onePremise wkRule neg
  -- exchangeRight [] [] Pa negPa [negQf]:
  -- [] -> [] ++ [Pa, negPa] ++ [negQf] ==> [] -> [] ++ [negPa, Pa] ++ [negQf]
  let e1Rule : FOLKStep1
      (Sequent.mk [] ([] ++ [Pa, negPa] ++ [negQf]))
      (Sequent.mk [] ([] ++ [negPa, Pa] ++ [negQf])) :=
    FOLKStep1.exchangeRight [] [] Pa negPa [negQf]
  let e1 : FOLKProofTree (Sequent.mk [] ([] ++ [negPa, Pa] ++ [negQf])) :=
    FOLKProofTree.onePremise e1Rule wk
  -- exchangeRight [] [negPa] Pa negQf []:
  -- [] -> [negPa] ++ [Pa, negQf] ++ [] ==> [] -> [negPa] ++ [negQf, Pa] ++ []
  let e2Rule : FOLKStep1
      (Sequent.mk [] ([negPa] ++ [Pa, negQf] ++ []))
      (Sequent.mk [] ([negPa] ++ [negQf, Pa] ++ [])) :=
    FOLKStep1.exchangeRight [] [negPa] Pa negQf []
  FOLKProofTree.onePremise e2Rule e1

helper /-- Helper: LK proof tree for the Qf branch of the Herbrand
    disjunction. Proves [] -> [neg Pa, neg Qf, Qf] by:
    Axiom [Qf]->[Qf], negRight, weakenRight neg Pa, three
    exchanges. Indexed by its conclusion sequent. -/
def herbrandEx_t2 :
    FOLKProofTree
      (Sequent.mk ([] : List (FormulaN herbrandExLang))
        [FormulaN.neg herbrandEx_Pa, FormulaN.neg herbrandEx_Qf,
         herbrandEx_Qf]) :=
  let Qf := herbrandEx_Qf
  let negPa := FormulaN.neg herbrandEx_Pa
  let negQf := FormulaN.neg Qf
  -- Axiom: [Qf] -> [Qf]
  let ax : FOLKProofTree (Sequent.mk [Qf] [Qf]) :=
    FOLKProofTree.axiom_ (Sequent.mk [Qf] [Qf]) ⟨Qf, rfl, rfl⟩
  -- negRight Qf [] [Qf]: [Qf] -> [Qf] ==> [] -> [Qf] ++ [negQf]
  let negRule : FOLKStep1
      (Sequent.mk (Qf :: []) [Qf])
      (Sequent.mk [] ([Qf] ++ [negQf])) :=
    FOLKStep1.negRight Qf [] [Qf]
  let neg : FOLKProofTree (Sequent.mk [] ([Qf] ++ [negQf])) :=
    FOLKProofTree.onePremise negRule ax
  -- weakenRight negPa [] [Qf, negQf]: [] -> [Qf, negQf] ==>
  -- [] -> [Qf, negQf] ++ [negPa]
  let wkRule : FOLKStep1
      (Sequent.mk [] [Qf, negQf])
      (Sequent.mk [] ([Qf, negQf] ++ [negPa])) :=
    FOLKStep1.weakenRight negPa [] [Qf, negQf]
  let wk : FOLKProofTree (Sequent.mk [] ([Qf, negQf] ++ [negPa])) :=
    FOLKProofTree.onePremise wkRule neg
  -- exchangeRight [] [] Qf negQf [negPa]:
  -- [] -> [] ++ [Qf, negQf] ++ [negPa] ==> [] -> [] ++ [negQf, Qf] ++ [negPa]
  let e1Rule : FOLKStep1
      (Sequent.mk [] ([] ++ [Qf, negQf] ++ [negPa]))
      (Sequent.mk [] ([] ++ [negQf, Qf] ++ [negPa])) :=
    FOLKStep1.exchangeRight [] [] Qf negQf [negPa]
  let e1 : FOLKProofTree (Sequent.mk [] ([] ++ [negQf, Qf] ++ [negPa])) :=
    FOLKProofTree.onePremise e1Rule wk
  -- exchangeRight [] [negQf] Qf negPa []:
  -- [] -> [negQf] ++ [Qf, negPa] ++ [] ==> [] -> [negQf] ++ [negPa, Qf] ++ []
  let e2Rule : FOLKStep1
      (Sequent.mk [] ([negQf] ++ [Qf, negPa] ++ []))
      (Sequent.mk [] ([negQf] ++ [negPa, Qf] ++ [])) :=
    FOLKStep1.exchangeRight [] [negQf] Qf negPa []
  let e2 : FOLKProofTree (Sequent.mk [] ([negQf] ++ [negPa, Qf] ++ [])) :=
    FOLKProofTree.onePremise e2Rule e1
  -- exchangeRight [] [] negQf negPa [Qf]:
  -- [] -> [] ++ [negQf, negPa] ++ [Qf] ==> [] -> [] ++ [negPa, negQf] ++ [Qf]
  let e3Rule : FOLKStep1
      (Sequent.mk [] ([] ++ [negQf, negPa] ++ [Qf]))
      (Sequent.mk [] ([] ++ [negPa, negQf] ++ [Qf])) :=
    FOLKStep1.exchangeRight [] [] negQf negPa [Qf]
  FOLKProofTree.onePremise e3Rule e2

helper /-- Helper: Full LK proof tree for the Herbrand disjunction,
    combining the Pa and Qf branches via andRight. Indexed by its
    conclusion sequent (= herbrandExDisjunction). -/
def herbrandEx_fullTree :
    FOLKProofTree herbrandExDisjunction :=
  let Pa := herbrandEx_Pa
  let Qf := herbrandEx_Qf
  let negPa := FormulaN.neg Pa
  let negQf := FormulaN.neg Qf
  -- andRight Pa Qf [] [negPa, negQf]:
  -- prem1 [] -> [negPa, negQf] ++ [Pa]
  -- prem2 [] -> [negPa, negQf] ++ [Qf]
  -- conc  [] -> [negPa, negQf] ++ [conj Pa Qf]
  let andRule : FOLKStep2
      (Sequent.mk [] ([negPa, negQf] ++ [Pa]))
      (Sequent.mk [] ([negPa, negQf] ++ [Qf]))
      (Sequent.mk [] ([negPa, negQf] ++ [FormulaN.conj Pa Qf])) :=
    FOLKStep2.andRight Pa Qf [] [negPa, negQf]
  FOLKProofTree.twoPremise andRule herbrandEx_t1 herbrandEx_t2

helper /-- Helper: The full proof tree has the Herbrand disjunction as its
    conclusion. With indexed FOLKProofTree this is by construction. -/
theorem herbrandEx_fullTree_conclusion :
    herbrandEx_fullTree.conclusion = herbrandExDisjunction := rfl

proof_of herbrandExDisjunctionProvable := ⟨herbrandEx_fullTree⟩
  -- BEGIN PROOF


end LCS.Herbrand.HerbrandTheorem.Main

end
