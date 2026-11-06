import LCS.Herbrand.HerbrandTheorem.Main.Example

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

proof_of herbrandExDisjunctionProvable := ⟨herbrandEx_fullTree⟩
  -- BEGIN PROOF

end LCS.Herbrand.HerbrandTheorem.Main
