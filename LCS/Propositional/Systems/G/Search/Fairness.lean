import LCS.Propositional.Systems.G.Search

namespace LCS.Propositional.Systems.G.Search

open LCS.Propositional.Syntax
open LCS.Propositional.Systems.G

/-- A rule principal together with its side; `true` denotes the succedent. -/
def rulePrincipal1 {p s : Sequent} : GentzenStep1 p s → Bool × PropFormulaNormalized
  | .andLeft _ _ _ A B => (false, .conj A B)
  | .orRight _ _ _ A B => (true, .disj A B)
  | .implRight _ _ _ A B => (true, .impl A B)
  | .negLeft _ _ _ A => (false, .neg A)
  | .negRight _ _ _ A => (true, .neg A)

def rulePrincipal2 {p q s : Sequent} : GentzenStep2 p q s → Bool × PropFormulaNormalized
  | .andRight _ _ _ A B => (true, .conj A B)
  | .orLeft _ _ _ A B => (false, .disj A B)
  | .implLeft _ _ _ A B => (false, .impl A B)

/-- An actual root-to-leaf path, recording precisely the inference principals.
    Equal sequent labels do not identify distinct paths. -/
inductive LeafPath : {s : Sequent} → DeductionTree s → Sequent →
    List (Bool × PropFormulaNormalized) → Prop where
  | leaf (s : Sequent) : LeafPath (.leaf s) s []
  | down {p s t : Sequent} {r : GentzenStep1 p s} {tree : DeductionTree p} {ps} :
      LeafPath tree t ps → LeafPath (.onePremise r tree) t (rulePrincipal1 r :: ps)
  | left {p q s t : Sequent} {r : GentzenStep2 p q s}
      {l : DeductionTree p} {rgt : DeductionTree q} {ps} :
      LeafPath l t ps → LeafPath (.twoPremise r l rgt) t (rulePrincipal2 r :: ps)
  | right {p q s t : Sequent} {r : GentzenStep2 p q s}
      {l : DeductionTree p} {rgt : DeductionTree q} {ps} :
      LeafPath rgt t ps → LeafPath (.twoPremise r l rgt) t (rulePrincipal2 r :: ps)

@[simp] theorem leafPath_cast {s s' t : Sequent} (eq : s = s')
    (tree : DeductionTree s) (ps) :
    LeafPath (eq ▸ tree) t ps ↔ LeafPath tree t ps := by
  subst eq
  rfl

/-- Replacing leaves concatenates genuine paths through the old and new trees. -/
theorem leafPath_mapLeaves {s t : Sequent} (tree : DeductionTree s)
    (expand : (s : Sequent) → DeductionTree s) {ps}
    (h : LeafPath (mapLeaves expand tree) t ps) :
    ∃ u before after, LeafPath tree u before ∧ LeafPath (expand u) t after ∧
      ps = before ++ after := by
  induction tree generalizing t ps with
  | leaf s => exact ⟨s, [], ps, .leaf s, h, rfl⟩
  | onePremise r tree ih =>
    cases h with
    | down h =>
      obtain ⟨u, before, after, hb, ha, rfl⟩ := ih h
      exact ⟨u, rulePrincipal1 r :: before, after, .down hb, ha, rfl⟩
  | twoPremise r l rgt ihl ihr =>
    cases h with
    | left h =>
      obtain ⟨u, before, after, hb, ha, rfl⟩ := ihl h
      exact ⟨u, rulePrincipal2 r :: before, after, .left hb, ha, rfl⟩
    | right h =>
      obtain ⟨u, before, after, hb, ha, rfl⟩ := ihr h
      exact ⟨u, rulePrincipal2 r :: before, after, .right hb, ha, rfl⟩

/-- The original unprocessed occurrences form literal suffixes. -/
def PendingSuffix (as bs : List PropFormulaNormalized) (s : Sequent) : Prop :=
  ∃ Γ Δ, s = ⟨Γ ++ as, Δ ++ bs⟩

theorem pendingSuffix_dropLeft {Γ Δ as bs : List PropFormulaNormalized} {A} :
    PendingSuffix as bs ⟨Γ ++ A :: as, Δ ++ bs⟩ := by
  refine ⟨Γ ++ [A], Δ, ?_⟩
  simp [List.append_assoc]

theorem scheduled_left_step (Γ Δ as bs : List PropFormulaNormalized)
    (A : PropFormulaNormalized) {t ps}
    (h : LeafPath (expandScheduled .systematic false as.length
      ⟨Γ ++ A :: as, Δ ++ bs⟩) t ps) (ho : ¬ isAxiom t) :
    PendingSuffix as bs t ∧ (isNonatomicFormula A → (false, A) ∈ ps) := by
  unfold expandScheduled at h
  split at h
  · next hf =>
    cases h
    refine ⟨pendingSuffix_dropLeft, ?_⟩
    intro hn
    have hall := (isFinishedLeafBool_iff _).mp hf
    rcases hall with hax | hall
    · exact False.elim (ho hax.2)
    · have ha := hall A (by simp)
      cases A <;> simp_all [isNonatomicFormula, isAtomicFormula]
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    unfold expandSelected at h
    split at h
    · next picked i hp =>
      have eq : A = picked ∧ Γ.length = i := by
        simpa only [LCS.Propositional.Systems.G.Search.selectOffset_suffix, Option.some.injEq, Prod.mk.injEq] using hp
      rcases eq with ⟨rfl, rfl⟩
      cases A with
      | var n =>
        simp only at h
        cases h
        exact ⟨pendingSuffix_dropLeft, False.elim⟩
      | neg C =>
        simp only [leafPath_cast] at h
        cases h with
        | down hl =>
          cases hl
          refine ⟨⟨Γ, C :: Δ, ?_⟩, ?_⟩
          · simp [List.drop_append]
          · simp [rulePrincipal1]
      | conj C D =>
        simp only [leafPath_cast] at h
        cases h with
        | down hl =>
          cases hl
          refine ⟨⟨Γ ++ [C, D], Δ, ?_⟩, ?_⟩
          · simp [List.drop_append]
          · simp [rulePrincipal1]
      | disj C D =>
        simp only [leafPath_cast] at h
        cases h with
        | left hl =>
          cases hl
          refine ⟨⟨Γ ++ [C], Δ, ?_⟩, ?_⟩
          · simp [List.drop_append]
          · simp [rulePrincipal2]
        | right hr =>
          cases hr
          refine ⟨⟨Γ ++ [D], Δ, ?_⟩, ?_⟩
          · simp [List.drop_append]
          · simp [rulePrincipal2]
      | impl C D =>
        simp only [leafPath_cast] at h
        cases h with
        | left hl =>
          cases hl
          refine ⟨⟨Γ, C :: Δ, ?_⟩, ?_⟩
          · simp [List.drop_append]
          · simp [rulePrincipal2]
        | right hr =>
          cases hr
          refine ⟨⟨D :: Γ, Δ, ?_⟩, ?_⟩
          · simp [List.drop_append]
          · simp [rulePrincipal2]
    · next hp => simp [LCS.Propositional.Systems.G.Search.selectOffset_suffix] at hp


theorem pendingSuffix_dropRight {Γ Δ as bs : List PropFormulaNormalized} {A} :
    PendingSuffix as bs ⟨Γ ++ as, Δ ++ A :: bs⟩ := by
  refine ⟨Γ, Δ ++ [A], ?_⟩
  simp [List.append_assoc]

theorem scheduled_right_step (Γ Δ as bs : List PropFormulaNormalized)
    (A : PropFormulaNormalized) {t ps}
    (h : LeafPath (expandScheduled .systematic true bs.length
      ⟨Γ ++ as, Δ ++ A :: bs⟩) t ps) (ho : ¬ isAxiom t) :
    PendingSuffix as bs t ∧ (isNonatomicFormula A → (true, A) ∈ ps) := by
  unfold expandScheduled at h
  split at h
  · next hf =>
    cases h
    refine ⟨pendingSuffix_dropRight, ?_⟩
    intro hn
    have hall := (isFinishedLeafBool_iff _).mp hf
    rcases hall with hax | hall
    · exact False.elim (ho hax.2)
    · have ha := hall A (by simp)
      cases A <;> simp_all [isNonatomicFormula, isAtomicFormula]
  · simp only [↓reduceIte] at h
    unfold expandSelected at h
    simp only at h
    split at h
    · next picked i hp =>
      have eq : A = picked ∧ Δ.length = i := by
        simpa only [LCS.Propositional.Systems.G.Search.selectOffset_suffix, Option.some.injEq, Prod.mk.injEq] using hp
      rcases eq with ⟨rfl, rfl⟩
      cases A with
      | var n =>
        simp only at h
        cases h
        exact ⟨pendingSuffix_dropRight, False.elim⟩
      | neg C =>
        simp only [leafPath_cast] at h
        cases h with
        | down hl =>
          cases hl
          refine ⟨⟨C :: Γ, Δ, ?_⟩, ?_⟩
          · simp [List.drop_append]
          · simp [rulePrincipal1]
      | conj C D =>
        simp only [leafPath_cast] at h
        cases h with
        | left hl =>
          cases hl
          refine ⟨⟨Γ, Δ ++ [C], ?_⟩, ?_⟩
          · simp [List.drop_append]
          · simp [rulePrincipal2]
        | right hr =>
          cases hr
          refine ⟨⟨Γ, Δ ++ [D], ?_⟩, ?_⟩
          · simp [List.drop_append]
          · simp [rulePrincipal2]
      | disj C D =>
        simp only [leafPath_cast] at h
        cases h with
        | down hl =>
          cases hl
          refine ⟨⟨Γ, Δ ++ [C, D], ?_⟩, ?_⟩
          · simp [List.drop_append]
          · simp [rulePrincipal1]
      | impl C D =>
        simp only [leafPath_cast] at h
        cases h with
        | down hl =>
          cases hl
          refine ⟨⟨C :: Γ, D :: Δ, ?_⟩, ?_⟩
          · simp [List.drop_append]
          · simp [rulePrincipal1]
    · next hp => simp [LCS.Propositional.Systems.G.Search.selectOffset_suffix] at hp

@[simp] theorem mapLeaves_leafIdentity {s} (tree : DeductionTree s) :
    mapLeaves (fun s => .leaf s) tree = tree := by
  induction tree <;> simp_all [mapLeaves]

theorem mapLeaves_compose {s} (tree : DeductionTree s)
    (f g : (s : Sequent) → DeductionTree s) :
    mapLeaves f (mapLeaves g tree) = mapLeaves (fun s => mapLeaves f (g s)) tree := by
  induction tree <;> simp_all [mapLeaves]

theorem expandSchedule_mapLeaves (mode : SearchMode) (schedule) {s} (tree : DeductionTree s) :
    expandSchedule mode schedule tree =
      mapLeaves (fun s => expandSchedule mode schedule (.leaf s)) tree := by
  induction schedule generalizing s tree with
  | nil => simp [expandSchedule]
  | cons e rest ih =>
    simp only [expandSchedule, List.foldl_cons]
    change expandSchedule mode rest (mapLeaves (expandScheduled mode e.1 e.2) tree) = _
    rw [ih, mapLeaves_compose]
    congr 1
    funext s
    simp only [mapLeaves]
    exact (ih _).symm

theorem expandSchedule_closed (schedule) {s} (hs : isAxiom s) :
    expandSchedule .systematic schedule (.leaf s) = .leaf s := by
  have hf : isFinishedLeafBool .systematic s = true :=
    (isFinishedLeafBool_iff s).mpr (.inl ⟨rfl, hs⟩)
  induction schedule with
  | nil => rfl
  | cons e rest ih =>
    simpa only [expandSchedule, List.foldl_cons, mapLeaves, expandScheduled, hf, ↓reduceIte] using ih

theorem leafPath_schedule_cons {s t} {e : Bool × Nat} {rest ps}
    (h : LeafPath (expandSchedule .systematic (e :: rest) (.leaf s)) t ps) :
    ∃ u before after,
      LeafPath (expandScheduled .systematic e.1 e.2 s) u before ∧
      LeafPath (expandSchedule .systematic rest (.leaf u)) t after ∧
      ps = before ++ after := by
  change LeafPath (expandSchedule .systematic rest (expandScheduled .systematic e.1 e.2 s)) t ps at h
  rw [expandSchedule_mapLeaves] at h
  exact leafPath_mapLeaves _ _ h

theorem schedule_open_start {s t} {schedule ps}
    (h : LeafPath (expandSchedule .systematic schedule (.leaf s)) t ps)
    (ho : ¬ isAxiom t) : ¬ isAxiom s := by
  intro hc
  rw [expandSchedule_closed schedule hc] at h
  cases h
  exact ho hc

/-- Every original succedent occurrence is processed along an open branch. -/
theorem right_schedule_fair (bs Γ Δ : List PropFormulaNormalized) {t ps}
    (h : LeafPath (expandSchedule .systematic (suffixSchedule true bs.length)
      (.leaf ⟨Γ ++ [], Δ ++ bs⟩)) t ps) (ho : ¬ isAxiom t) :
    ∀ A ∈ bs, isNonatomicFormula A → (true, A) ∈ ps := by
  induction bs generalizing Γ Δ ps with
  | nil => simp
  | cons B bs ih =>
    rw [List.length_cons, LCS.Propositional.Systems.G.Search.suffixSchedule_succ] at h
    obtain ⟨u, before, after, hb, ha, rfl⟩ := leafPath_schedule_cons h
    have hu := schedule_open_start ha ho
    have hs := scheduled_right_step Γ Δ [] bs B hb hu
    obtain ⟨Γ', Δ', rfl⟩ := hs.1
    have tail := ih Γ' Δ' ha
    intro A hA hn
    rcases List.mem_cons.mp hA with rfl | hA
    · exact List.mem_append_left _ (hs.2 hn)
    · exact List.mem_append_right _ (tail A hA hn)

/-- The suffix invariant proves fairness for the entire frozen occurrence list.
    Prefixes may contain arbitrary formulas, including formulas equal to a queued
    occurrence. They do not change which occurrence is expanded next. -/
theorem frozen_schedule_fair (as bs Γ Δ : List PropFormulaNormalized) {t ps}
    (h : LeafPath (expandSchedule .systematic
      (suffixSchedule false as.length ++ suffixSchedule true bs.length)
      (.leaf ⟨Γ ++ as, Δ ++ bs⟩)) t ps) (ho : ¬ isAxiom t) :
    (∀ A ∈ as, isNonatomicFormula A → (false, A) ∈ ps) ∧
    (∀ B ∈ bs, isNonatomicFormula B → (true, B) ∈ ps) := by
  induction as generalizing Γ Δ ps with
  | nil =>
    refine ⟨by simp, ?_⟩
    apply right_schedule_fair bs Γ Δ (ho := ho)
    simpa [suffixSchedule] using h
  | cons A as ih =>
    rw [List.length_cons, LCS.Propositional.Systems.G.Search.suffixSchedule_succ, List.cons_append] at h
    obtain ⟨u, before, after, hb, ha, rfl⟩ := leafPath_schedule_cons h
    have hu := schedule_open_start ha ho
    have hs := scheduled_left_step Γ Δ as bs A hb hu
    obtain ⟨Γ', Δ', rfl⟩ := hs.1
    obtain ⟨hleft, hright⟩ := ih Γ' Δ' ha
    constructor
    · intro B hB hn
      rcases List.mem_cons.mp hB with rfl | hB
      · exact List.mem_append_left _ (hs.2 hn)
      · exact List.mem_append_right _ (hleft B hB hn)
    · intro B hB hn
      exact List.mem_append_right _ (hright B hB hn)


/-- Proof of Lemma 3.5.2 (finite-round fairness): each nonatomic formula
    present at the start is a principal on every surviving open branch. -/
theorem expandLeaf_open_fair {s t : Sequent} {ps}
    (h : LeafPath (expandLeaf .systematic s) t ps) (ho : ¬ isAxiom t) :
    (∀ A ∈ s.antecedent, isNonatomicFormula A → (false, A) ∈ ps) ∧
    (∀ B ∈ s.succedent, isNonatomicFormula B → (true, B) ∈ ps) := by
  rw [LCS.Propositional.Systems.G.Search.expandLeaf_eq_full_schedule] at h
  cases s with
  | mk as bs => exact frozen_schedule_fair as bs [] [] h ho

/-- Closed nodes are leaves: every node carrying a rule is nonaxiomatic. -/
def AllInnerOpen : {s : Sequent} → DeductionTree s → Prop
  | _, .leaf _ => True
  | s, .onePremise _ child => ¬ isAxiom s ∧ AllInnerOpen child
  | s, .twoPremise _ left right => ¬ isAxiom s ∧ AllInnerOpen left ∧ AllInnerOpen right

@[simp] theorem allInnerOpen_cast {s s'} (eq : s = s') (tree : DeductionTree s) :
    AllInnerOpen (eq ▸ tree) ↔ AllInnerOpen tree := by
  subst eq
  rfl

theorem allInnerOpen_selected {s} (a b) (ha hb) (ho : ¬ isAxiom s) :
    AllInnerOpen (expandSelected s a b ha hb) := by
  unfold expandSelected
  split
  · next A i =>
    have hs := ha A i rfl
    cases A <;> simp only [allInnerOpen_cast, AllInnerOpen, and_true]
    all_goals first | trivial | simpa only [isAxiom, ← hs] using ho
  · split
    · next B i =>
      have hs := hb B i rfl
      cases B <;> simp only [allInnerOpen_cast, AllInnerOpen, and_true]
      all_goals first | trivial | simpa only [isAxiom, ← hs] using ho
    · trivial

theorem allInnerOpen_scheduled (side offset s) :
    AllInnerOpen (expandScheduled .systematic side offset s) := by
  unfold expandScheduled
  split
  · trivial
  · next hf =>
    have ho : ¬ isAxiom s := fun hs =>
      hf ((isFinishedLeafBool_iff s).mpr (.inl ⟨rfl, hs⟩))
    split <;> exact allInnerOpen_selected _ _ _ _ ho

theorem allInnerOpen_mapLeaves {s} (tree : DeductionTree s)
    (f : (s : Sequent) → DeductionTree s)
    (ht : AllInnerOpen tree) (hf : ∀ s, AllInnerOpen (f s)) :
    AllInnerOpen (mapLeaves f tree) := by
  induction tree with
  | leaf s => exact hf s
  | onePremise r child ih => exact ⟨ht.1, ih ht.2⟩
  | twoPremise r l rgt ihl ihr => exact ⟨ht.1, ihl ht.2.1, ihr ht.2.2⟩

theorem allInnerOpen_schedule (schedule) {s} (tree : DeductionTree s)
    (ht : AllInnerOpen tree) : AllInnerOpen (expandSchedule .systematic schedule tree) := by
  induction schedule generalizing tree with
  | nil => exact ht
  | cons e rest ih =>
    exact ih _ (allInnerOpen_mapLeaves _ _ ht (allInnerOpen_scheduled e.1 e.2))

theorem allInnerOpen_expandLeaf (s : Sequent) : AllInnerOpen (expandLeaf .systematic s) := by
  rw [LCS.Propositional.Systems.G.Search.expandLeaf_eq_full_schedule]
  exact allInnerOpen_schedule _ _ trivial


/-- A leaf path with its exact address. Unary and left edges use `0`, right
    edges use `1`, matching the infinite search tree's address convention. -/
inductive AddressedLeafPath : {s : Sequent} → DeductionTree s → List Nat →
    Sequent → List (Bool × PropFormulaNormalized) → Prop where
  | leaf (s) : AddressedLeafPath (.leaf s) [] s []
  | down {p s t} {r : GentzenStep1 p s} {tree : DeductionTree p} {address ps} :
      AddressedLeafPath tree address t ps →
      AddressedLeafPath (.onePremise r tree) (0 :: address) t (rulePrincipal1 r :: ps)
  | left {p q s t} {r : GentzenStep2 p q s} {l : DeductionTree p} {rgt : DeductionTree q}
      {address ps} : AddressedLeafPath l address t ps →
      AddressedLeafPath (.twoPremise r l rgt) (0 :: address) t (rulePrincipal2 r :: ps)
  | right {p q s t} {r : GentzenStep2 p q s} {l : DeductionTree p} {rgt : DeductionTree q}
      {address ps} : AddressedLeafPath rgt address t ps →
      AddressedLeafPath (.twoPremise r l rgt) (1 :: address) t (rulePrincipal2 r :: ps)

theorem AddressedLeafPath.forget {s t tree address ps}
    (h : @AddressedLeafPath s tree address t ps) : LeafPath tree t ps := by
  induction h with
  | leaf s => exact .leaf s
  | down _ ih => exact .down ih
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

/-- An actual rule edge at a specified address, retaining its parent, child,
    chosen branch, and principal. -/
inductive RuleEdgeAt : {s : Sequent} → DeductionTree s → List Nat → Nat →
    Sequent → Sequent → (Bool × PropFormulaNormalized) → Prop where
  | rootOne {p s} (r : GentzenStep1 p s) (tree : DeductionTree p) :
      RuleEdgeAt (.onePremise r tree) [] 0 s p (rulePrincipal1 r)
  | rootLeft {p q s} (r : GentzenStep2 p q s) (l : DeductionTree p) (rgt : DeductionTree q) :
      RuleEdgeAt (.twoPremise r l rgt) [] 0 s p (rulePrincipal2 r)
  | rootRight {p q s} (r : GentzenStep2 p q s) (l : DeductionTree p) (rgt : DeductionTree q) :
      RuleEdgeAt (.twoPremise r l rgt) [] 1 s q (rulePrincipal2 r)
  | down {p s u v} {r : GentzenStep1 p s} {tree : DeductionTree p}
      {address dir sf} : RuleEdgeAt tree address dir u v sf →
      RuleEdgeAt (.onePremise r tree) (0 :: address) dir u v sf
  | left {p q s u v} {r : GentzenStep2 p q s} {l : DeductionTree p} {rgt : DeductionTree q}
      {address dir sf} : RuleEdgeAt l address dir u v sf →
      RuleEdgeAt (.twoPremise r l rgt) (0 :: address) dir u v sf
  | right {p q s u v} {r : GentzenStep2 p q s} {l : DeductionTree p} {rgt : DeductionTree q}
      {address dir sf} : RuleEdgeAt rgt address dir u v sf →
      RuleEdgeAt (.twoPremise r l rgt) (1 :: address) dir u v sf

/-- A recorded principal comes from an actual edge on the same addressed path. -/
theorem AddressedLeafPath.principal_event {s t tree address ps sf}
    (h : @AddressedLeafPath s tree address t ps) (hm : sf ∈ ps) :
    ∃ edgeAddress dir parent child,
      RuleEdgeAt tree edgeAddress dir parent child sf ∧
      (edgeAddress ++ [dir]).IsPrefix address := by
  induction h with
  | leaf s => simp at hm
  | @down p s t r tree address ps hp ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨[], 0, s, p, .rootOne r tree, ⟨address, rfl⟩⟩
    · obtain ⟨q, d, u, v, he, suffix, hs⟩ := ih hm
      exact ⟨0 :: q, d, u, v, .down he, ⟨suffix, by simp only [List.cons_append, hs]⟩⟩
  | @left p q s t r l rgt address ps hp ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨[], 0, s, p, .rootLeft r l rgt, ⟨address, rfl⟩⟩
    · obtain ⟨q, d, u, v, he, suffix, hs⟩ := ih hm
      exact ⟨0 :: q, d, u, v, .left he, ⟨suffix, by simp only [List.cons_append, hs]⟩⟩
  | @right p q s t r l rgt address ps hp ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨[], 1, s, q, .rootRight r l rgt, ⟨address, rfl⟩⟩
    · obtain ⟨q, d, u, v, he, suffix, hs⟩ := ih hm
      exact ⟨1 :: q, d, u, v, .right he, ⟨suffix, by simp only [List.cons_append, hs]⟩⟩

/-- Fairness with an actual rule witness on a prefix of the selected branch. -/
theorem expandLeaf_addressed_fair {s t address ps side A}
    (h : AddressedLeafPath (expandLeaf .systematic s) address t ps)
    (ho : ¬ isAxiom t)
    (hm : A ∈ if side then s.succedent else s.antecedent)
    (hn : isNonatomicFormula A) :
    ∃ edgeAddress dir parent child,
      RuleEdgeAt (expandLeaf .systematic s) edgeAddress dir parent child (side, A) ∧
      (edgeAddress ++ [dir]).IsPrefix address := by
  apply h.principal_event
  have hf := expandLeaf_open_fair h.forget ho
  cases side with
  | false => exact hf.1 A hm hn
  | true => exact hf.2 A hm hn


private theorem treeCast_heq {s s'} (h : s = s') (t : DeductionTree s) :
    HEq (h ▸ t) t := by
  subst h
  rfl

private theorem implTree_heq (Γ Δ Γ' Δ' Λ : List PropFormulaNormalized)
    (A B : PropFormulaNormalized) (hΓ : Γ = Γ') (hΔ : Δ = Δ') :
    HEq (DeductionTree.twoPremise (GentzenStep2.implLeft Γ Δ Λ A B)
      (.leaf ⟨Γ ++ Δ, A :: Λ⟩) (.leaf ⟨[B] ++ Γ ++ Δ, Λ⟩))
      (DeductionTree.twoPremise (GentzenStep2.implLeft Γ' Δ' Λ A B)
      (.leaf ⟨Γ' ++ Δ', A :: Λ⟩) (.leaf ⟨[B] ++ Γ' ++ Δ', Λ⟩)) := by
  subst hΓ
  subst hΔ
  rfl

private theorem mapLeaves_cast {s s'} (h : s = s') (t : DeductionTree s)
    (f : (s : Sequent) → DeductionTree s) :
    mapLeaves f (h ▸ t) = h ▸ mapLeaves f t := by
  subst h
  rfl

/-- The single inference generated by a final implication after an atomic prefix. -/
def finalImplicationTree (Γ : List PropFormulaNormalized) (a b q : Nat) :
    DeductionTree ⟨Γ ++ [.impl (.var a) (.var b)], [.var q]⟩ :=
  (show (⟨Γ ++ [.impl (.var a) (.var b)] ++ [], [.var q]⟩ : Sequent) =
      ⟨Γ ++ [.impl (.var a) (.var b)], [.var q]⟩ from by simp) ▸
    .twoPremise (GentzenStep2.implLeft Γ [] [.var q] (.var a) (.var b))
      (.leaf ⟨Γ ++ [], [.var a, .var q]⟩)
      (.leaf ⟨[.var b] ++ Γ ++ [], [.var q]⟩)

theorem expandScheduled_finalImplication (Γ : List PropFormulaNormalized) (a b q : Nat)
    (ho : ¬isAxiom ⟨Γ ++ [.impl (.var a) (.var b)], [.var q]⟩) :
    expandScheduled .systematic false 0 ⟨Γ ++ [.impl (.var a) (.var b)], [.var q]⟩ =
      finalImplicationTree Γ a b q := by
  have hf : ¬isFinishedLeafBool .systematic
      ⟨Γ ++ [.impl (.var a) (.var b)], [.var q]⟩ = true := by
    intro h
    rcases (isFinishedLeafBool_iff _).mp h with h | h
    · exact ho h.2
    · have hn := h (.impl (.var a) (.var b)) (by simp)
      exact hn
  unfold expandScheduled
  simp only [hf, Bool.false_eq_true, ↓reduceIte]
  unfold expandSelected
  split
  · next A i hi =>
    have he : (PropFormulaNormalized.impl (.var a) (.var b), Γ.length) = (A, i) := by
      apply Option.some.inj
      exact (LCS.Propositional.Systems.G.Search.selectOffset_suffix Γ [] (.impl (.var a) (.var b))).symm.trans hi
    cases he
    simp only
    apply eq_of_heq
    unfold finalImplicationTree
    exact (treeCast_heq _ _).trans
      ((implTree_heq _ _ _ _ _ _ _ (by simp) (by simp [List.drop_append])).trans
        (treeCast_heq _ _).symm)
  · next hn =>
    have he := LCS.Propositional.Systems.G.Search.selectOffset_suffix Γ [] (.impl (.var a) (.var b))
    cases hn.symm.trans he

/-- Example 3.5.2's logical expansion consists of exactly one implication rule. -/
theorem expandLeaf_finalImplication (Γ : List PropFormulaNormalized) (a b q : Nat)
    (hat : Γ.all isAtomicBool = true)
    (ho : ¬isAxiom ⟨Γ ++ [.impl (.var a) (.var b)], [.var q]⟩) :
    expandLeaf .systematic ⟨Γ ++ [.impl (.var a) (.var b)], [.var q]⟩ =
      finalImplicationTree Γ a b q := by
  rw [LCS.Propositional.Systems.G.Search.expandLeaf_eq_full_schedule]
  have hskip := LCS.Propositional.Systems.G.Search.expandSchedule_skip_atomic_prefix (mode := .systematic)
    (⟨Γ ++ [.impl (.var a) (.var b)], [.var q]⟩ : Sequent) false [] Γ
    [.impl (.var a) (.var b)] (suffixSchedule true 1) (by simp)
    (fun A hA => (isAtomicBool_iff A).mp ((List.all_eq_true.mp hat) A hA))
  simp only [List.length_append, List.length_cons, List.length_nil] at hskip ⊢
  rw [hskip]
  simp only [suffixSchedule, List.range_succ, List.range_zero, List.nil_append,
    List.reverse_cons, List.reverse_nil, List.map_cons, List.map_nil,
    List.cons_append, expandSchedule, List.foldl_cons, List.foldl_nil, mapLeaves]
  rw [expandScheduled_finalImplication Γ a b q ho]
  unfold finalImplicationTree
  rw [mapLeaves_cast]
  congr 1
  simp only [mapLeaves]
  congr 1
  · apply LCS.Propositional.Systems.G.Search.expandScheduled_var (i := 1) (n := q)
    rfl
  · apply LCS.Propositional.Systems.G.Search.expandScheduled_var (i := 0) (n := q)
    rfl

end LCS.Propositional.Systems.G.Search
