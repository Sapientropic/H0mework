import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Responsibility
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Finance
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.SelfDeviation.Comparison.Appraisal.Price

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Appraisal
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
namespace Original
abbrev Prices := World.Input.Event.SelfDeviation.Comparison.Appraisal.Prices
abbrev Agency := World.Input.Event.SelfDeviation.Comparison.Appraisal.Agency
abbrev goods := World.Input.Event.SelfDeviation.Comparison.Appraisal.goods
end Original
variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (authority : ScopeRevision.Ready old)
  {originInputs : List (List Action)} (inventory : Pending.Joint.Inventory authority originInputs)
  (fresh : Handoff.Ready (Pending.B authority) (Future.advance authority inventory .revision).inputs) (count : Nat)

def paidWindow (word : List Action) : Bool := (Registered.assess authority inventory fresh word).isPaid

theorem paid_window_keeps_the_actual_service_receipt (word : List Action) :
    paidWindow authority inventory fresh word = true ↔
      Registered.Legal authority inventory fresh word ∧ ∀ index, Registered.SlotPaid authority inventory fresh word index :=
  Registered.actual_paid_is_checked_not_supplied authority inventory fresh word

def alternatives (word : List Action) (intent : World.Input.Intent) (actor : Bool) : List World.Input.Method :=
  ((World.Input.menu (World.Epoch.ofFresh fresh) intent (Loss.cursorAt authority inventory fresh word count).before).filter fun choice =>
    decide (World.Input.Legal (World.Epoch.ofFresh fresh) intent (Loss.cursorAt authority inventory fresh word count).before choice ∧
      World.Input.Event.SelfDeviation.LocalWord actor
        (World.Input.candidate (World.Epoch.ofFresh fresh) intent (Loss.cursorAt authority inventory fresh word count).before choice))).map (·.method)

def agency (word : List Action) : Original.Agency where
  scope := fresh.scope
  technology := (Loss.cursorAt authority inventory fresh word count).before.technology
  kind := if paidWindow authority inventory fresh word then .paid else .replacementBlocked
  clock := (Loss.cursorAt authority inventory fresh word count).before.clock
  standing := fun actor => decide (actor ∈ Delegation.members fresh.scope.task)
  eligible := fun intent => decide (World.Input.Eligible (World.Epoch.ofFresh fresh) intent (Loss.cursorAt authority inventory fresh word count).before)
  available := alternatives authority inventory fresh count word
  exitMaterial := decide (World.Input.ExitCapacity.Envelope (Loss.cursorAt authority inventory fresh word count).before)

theorem every_listed_method_is_legal_and_self_controlled (word : List Action) (intent : World.Input.Intent)
    (actor : Bool) (method : World.Input.Method)
    (listed : method ∈ (agency authority inventory fresh count word).available intent actor) :
    ∃ choice ∈ World.Input.menu (World.Epoch.ofFresh fresh) intent (Loss.cursorAt authority inventory fresh word count).before,
      choice.method = method ∧ World.Input.Legal (World.Epoch.ofFresh fresh) intent (Loss.cursorAt authority inventory fresh word count).before choice ∧
      World.Input.Event.SelfDeviation.LocalWord actor
        (World.Input.candidate (World.Epoch.ofFresh fresh) intent (Loss.cursorAt authority inventory fresh word count).before choice) := by
  obtain ⟨choice,inside,same⟩ := List.mem_map.mp listed
  have checked := List.mem_filter.mp inside
  exact ⟨choice,checked.1,same,(of_decide_eq_true checked.2).1,(of_decide_eq_true checked.2).2⟩

variable {unit : Good} (price : Original.Prices unit)

def rawValues (book : Book) (paid : Bool) (actor : Bool) : List ℚ := book.flatMap fun entry =>
  Original.goods.map fun good => price.rate good *
    (if paid then entry.account.paid (actor,good) else entry.account.remaining (actor,good))
def rawQuantityValues (book : Book) (actor : Bool) : List ℚ := book.flatMap fun entry =>
  Original.goods.map fun good => price.rate good *
    Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Raw.quantity entry.original (actor,good)
def rawValue (book : Book) (actor : Bool) := (rawValues price book false actor).sum + (rawValues price book true actor).sum

theorem all_dynamic_original_cells_keep_their_own_priced_quantity (book : Book) (actor : Bool) :
    rawValue price book actor = (rawQuantityValues price book actor).sum := by
  unfold rawValue
  induction book with
  | nil => simp [rawValues,rawQuantityValues]
  | cons entry rest ih =>
    have cell : (Original.goods.map fun good => price.rate good * entry.account.remaining (actor,good)).sum +
        (Original.goods.map fun good => price.rate good * entry.account.paid (actor,good)).sum =
        (Original.goods.map fun good => price.rate good *
          Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Raw.quantity entry.original (actor,good)).sum := by
      rw [← List.sum_map_add]
      apply congrArg List.sum
      apply List.map_congr_left
      intro good _
      rw [← mul_add,entry.account.balance]
      rfl
    simp only [rawValues,rawQuantityValues,List.flatMap_cons,List.sum_append,Bool.false_eq_true,if_false,if_true] at *
    linarith only [cell,ih]

theorem newly_born_raw_quantities_cannot_be_cancelled_as_a_fixed_cohort (first last : Book) (actor : Bool) :
    rawValue price last actor - rawValue price first actor =
      (rawQuantityValues price last actor).sum - (rawQuantityValues price first actor).sum := by
  rw [all_dynamic_original_cells_keep_their_own_priced_quantity,all_dynamic_original_cells_keep_their_own_priced_quantity]

variable {unit : Good} (price : Original.Prices unit) (word : List Action) (actor : Bool)
def slotValues : List ℚ := (Responsibility.slots authority inventory fresh word (Loss.cursorAt authority inventory fresh word count).state).map fun item => price.slot item.origin item.value actor
def eventValues : List ℚ := (Responsibility.events authority inventory fresh word (Loss.cursorAt authority inventory fresh word count).state).map fun item => price.event item.origin item.value actor
def agencyValue := World.Input.Event.SelfDeviation.Comparison.Appraisal.agencyScore price actor (agency authority inventory fresh count word)
def timeCost := price.time actor * ((Loss.cursorAt authority inventory fresh word count).before.clock - (Handoff.start fresh).clock)
def value := (slotValues authority inventory fresh count price word actor).sum + (eventValues authority inventory fresh count price word actor).sum +
  agencyValue authority inventory fresh count price word actor - timeCost authority inventory fresh count price word actor -
    rawValue price (Loss.cursorAt authority inventory fresh word count).book actor
def financial (side : Bool) := (Original.goods.map fun good => price.rate good * Finance.account authority inventory fresh word count side actor good).sum
def expense := financial authority inventory fresh count price word actor true + financial authority inventory fresh count price word actor false
def payoff := value authority inventory fresh count price word actor - expense authority inventory fresh count price word actor

theorem the_financial_sum_is_the_original_actual_net_change : expense authority inventory fresh count price word actor =
    (Original.goods.map fun good => price.rate good *
      (Finance.quotedBefore authority inventory fresh word actor good - Finance.quotedAfter authority inventory fresh word count actor good)).sum := by
  unfold expense financial
  rw [← List.sum_map_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro good _
  rw [← mul_add,Finance.the_complete_continuation_net_has_one_original_start_and_actual_end]

variable (replacement : List Action)
def costs : List ℚ :=
  (Original.goods.map fun good => price.rate good * (Finance.account authority inventory fresh replacement count false actor good -
    Finance.account authority inventory fresh word count false actor good)) ++
  (slotValues authority inventory fresh count price word actor) ++
  ((slotValues authority inventory fresh count price replacement actor).map Neg.neg) ++
  (eventValues authority inventory fresh count price word actor) ++
  ((eventValues authority inventory fresh count price replacement actor).map Neg.neg) ++
  [agencyValue authority inventory fresh count price word actor - agencyValue authority inventory fresh count price replacement actor,
   timeCost authority inventory fresh count price replacement actor - timeCost authority inventory fresh count price word actor] ++
  rawValues price (Loss.cursorAt authority inventory fresh replacement count).book false actor ++
  rawValues price (Loss.cursorAt authority inventory fresh replacement count).book true actor ++
  (rawValues price (Loss.cursorAt authority inventory fresh word count).book false actor).map Neg.neg ++
  (rawValues price (Loss.cursorAt authority inventory fresh word count).book true actor).map Neg.neg
def budget := ((costs authority inventory fresh count price word actor replacement).map fun cost => max 0 cost).sum
def gains := ((costs authority inventory fresh count price word actor replacement).map fun cost => max 0 (-cost)).sum

private theorem neg_sum (entries : List ℚ) : (entries.map Neg.neg).sum = -entries.sum := by
  induction entries with
  | nil => simp
  | cons entry rest ih => simp only [List.map_cons,List.sum_cons,ih]; ring
private theorem weighted_sub {α : Type} (entries : List α) (left right weight : α → ℚ) :
    (entries.map fun item => weight item * (left item - right item)).sum =
      (entries.map fun item => weight item * left item).sum - (entries.map fun item => weight item * right item).sum := by
  induction entries with
  | nil => simp
  | cons entry rest ih => simp only [List.map_cons,List.sum_cons,ih]; ring

theorem every_native_cost_and_benefit_enters_the_same_payoff_difference :
    (costs authority inventory fresh count price word actor replacement).sum =
      financial authority inventory fresh count price replacement actor false - financial authority inventory fresh count price word actor false +
        value authority inventory fresh count price word actor - value authority inventory fresh count price replacement actor := by
  simp only [costs,List.sum_append,List.sum_cons,List.sum_nil,add_zero,neg_sum,weighted_sub]
  unfold financial value rawValue
  ring

private theorem positive_part (quantity : ℚ) : max 0 quantity - max 0 (-quantity) = quantity := by
  by_cases positive : 0 ≤ quantity
  · rw [max_eq_right positive,max_eq_left (neg_nonpos.mpr positive)]; ring
  · have negative := le_of_not_ge positive
    rw [max_eq_left negative,max_eq_right (neg_nonneg.mpr negative)]; ring

theorem the_budget_minus_all_gains_is_the_exact_signed_cost :
    budget authority inventory fresh count price word actor replacement - gains authority inventory fresh count price word actor replacement =
      (costs authority inventory fresh count price word actor replacement).sum := by
  unfold budget gains
  generalize costs authority inventory fresh count price word actor replacement = entries
  induction entries with
  | nil => simp
  | cons entry rest ih => simp only [List.map_cons,List.sum_cons]; linarith only [ih,positive_part entry]

variable (baseline : List Action)
def Available (candidate : List Action) : Prop := Registered.Legal authority inventory fresh candidate ∧
  World.Input.Event.SelfDeviation.LocalWord actor candidate
instance (candidate : List Action) : Decidable (Available authority inventory fresh actor candidate) := by
  unfold Available Registered.Legal
  infer_instance

theorem a_checked_incoming_word_is_legal_and_controlled_at_its_actual_start (candidate : List Action)
    (checked : Available authority inventory fresh actor candidate) :
    Registered.Legal authority inventory fresh candidate ∧
      World.Input.Event.SelfDeviation.LocalWord actor (Registered.actual authority inventory fresh candidate).submitted := by
  rw [(Registered.literal_input_and_original_in_window_cut authority inventory fresh candidate).1]
  exact checked

def sameWindow (candidate : List Action) : Bool :=
  decide (Available authority inventory fresh actor candidate) &&
  paidWindow authority inventory fresh baseline &&
  paidWindow authority inventory fresh candidate &&
  decide ((Loss.cursorAt authority inventory fresh baseline count).before.clock =
    (Loss.cursorAt authority inventory fresh candidate count).before.clock)

theorem every_checked_window_has_its_own_actual_payment_cut_and_signature (candidate : List Action)
    (checked : sameWindow authority inventory fresh count actor baseline candidate = true) :
    Available authority inventory fresh actor candidate ∧
    (Registered.Legal authority inventory fresh baseline ∧ ∀ index, Registered.SlotPaid authority inventory fresh baseline index) ∧
    (Registered.Legal authority inventory fresh candidate ∧ ∀ index, Registered.SlotPaid authority inventory fresh candidate index) ∧
    (Loss.cursorAt authority inventory fresh baseline count).before.clock =
      (Loss.cursorAt authority inventory fresh candidate count).before.clock := by
  simp only [sameWindow,Bool.and_eq_true_iff,decide_eq_true_eq] at checked
  exact ⟨checked.1.1.1,(paid_window_keeps_the_actual_service_receipt _ _ _ _).mp checked.1.1.2,
    (paid_window_keeps_the_actual_service_receipt _ _ _ _).mp checked.1.2,checked.2⟩

/-- A personal service attempt supplies the original task, without borrowing
another person's challenge or financing signature. Actual legality and payment
are checked after the same source executes it. -/
def personal (party : Bool) : List Action :=
  let before := Handoff.start fresh
  let needed := (((source fresh).seed.task.slots.flatMap (·.goods)).map fun item =>
    if item.1 = .service then item.2 else 0).sum + 1
  let count := (Rat.ceil ((needed - before.stock party .service) / 3)).toNat
  let production := Handoff.affordableProduction fresh before party count
  let supply := (source fresh).seed.task.slots.filterMap fun slot =>
    if slot.bearer = party then none else
      some (⟨party,[],.resource,[],.transfer party slot.bearer slot.goods⟩ : Action)
  let after := (law fresh).next before (production ++ supply)
  let proposal := Mandate.request fresh.scope after party (.propose party)
  let accepted := Mandate.request fresh.scope ((law fresh).step after proposal) party .accept
  production ++ supply ++ [proposal,accepted] ++
    (source fresh).seed.task.slots.map fun slot =>
      ⟨party,[],.service,[.service],.use slot.bearer slot.goods slot.purpose⟩

def menu : List (List Action) := [personal authority inventory fresh false,personal authority inventory fresh true,
  Handoff.firstWord fresh] ++ Handoff.methods.map (Handoff.candidate fresh (Handoff.start fresh))
def improvements : List (List Action) := (menu authority inventory fresh).filter fun candidate =>
  sameWindow authority inventory fresh count actor baseline candidate &&
  decide (payoff authority inventory fresh count price baseline actor < payoff authority inventory fresh count price candidate actor)
def stable : Bool := (improvements authority inventory fresh count price actor baseline).isEmpty

theorem computed_stability_checks_every_actual_same_window_response
    (checked : stable authority inventory fresh count price actor baseline = true)
    (candidate : List Action) (generated : candidate ∈ menu authority inventory fresh)
    (window : sameWindow authority inventory fresh count actor baseline candidate = true) :
    payoff authority inventory fresh count price candidate actor ≤ payoff authority inventory fresh count price baseline actor := by
  have empty := List.nil_of_isEmpty checked
  by_contra better
  have inside : candidate ∈ improvements authority inventory fresh count price actor baseline :=
    List.mem_filter.mpr ⟨generated,by simp only [window,Bool.true_and,decide_eq_true_eq]; exact lt_of_not_ge better⟩
  rw [empty] at inside
  cases inside

theorem computed_stability_bounds_the_original_selected_net
    (checked : stable authority inventory fresh count price actor baseline = true)
    (candidate : List Action) (generated : candidate ∈ menu authority inventory fresh)
    (window : sameWindow authority inventory fresh count actor baseline candidate = true) :
    financial authority inventory fresh count price baseline actor true - financial authority inventory fresh count price candidate actor true ≤
      budget authority inventory fresh count price baseline actor candidate - gains authority inventory fresh count price baseline actor candidate := by
  have compared := computed_stability_checks_every_actual_same_window_response authority inventory fresh count price actor baseline checked candidate generated window
  rw [the_budget_minus_all_gains_is_the_exact_signed_cost,every_native_cost_and_benefit_enters_the_same_payoff_difference]
  unfold payoff expense at compared
  linarith only [compared]

theorem every_computed_improvement_has_its_real_paid_window (candidate : List Action)
    (generated : candidate ∈ improvements authority inventory fresh count price actor baseline) :
    candidate ∈ menu authority inventory fresh ∧ sameWindow authority inventory fresh count actor baseline candidate = true ∧
      payoff authority inventory fresh count price baseline actor < payoff authority inventory fresh count price candidate actor := by
  have selected := List.mem_filter.mp generated
  exact ⟨selected.1,(Bool.and_eq_true_iff.mp selected.2).1,of_decide_eq_true (Bool.and_eq_true_iff.mp selected.2).2⟩


inductive Decision where
  | private unpaid (denied : paidWindow authority inventory fresh baseline = false)
  | private improvement (candidate : List Action)
      (generated : candidate ∈ improvements authority inventory fresh count price actor baseline)
  | private stable (paid : paidWindow authority inventory fresh baseline = true)
      (checked : stable authority inventory fresh count price actor baseline = true)

def classify : Decision authority inventory fresh count price actor baseline :=
  if paid : paidWindow authority inventory fresh baseline = true then
    match selected : (improvements authority inventory fresh count price actor baseline).head? with
    | some candidate => .improvement candidate (List.mem_of_mem_head? selected)
    | none => .stable paid (by
        have empty := List.head?_eq_none_iff.mp selected
        simp only [stable,empty,List.isEmpty_nil])
  else .unpaid (by cases value : paidWindow authority inventory fresh baseline <;> simp_all)

def Decision.selected : Decision authority inventory fresh count price actor baseline → Option (List Action)
  | .improvement candidate _ => some candidate
  | .stable .. | .unpaid _ => none

theorem the_source_produces_an_unpaid_baseline_or_actual_improvement_or_paid_cost_bound :
    (paidWindow authority inventory fresh baseline = false ∧
      (classify authority inventory fresh count price actor baseline).selected = none) ∨
    (∃ candidate, (classify authority inventory fresh count price actor baseline).selected = some candidate ∧
      candidate ∈ menu authority inventory fresh ∧ sameWindow authority inventory fresh count actor baseline candidate = true ∧
      payoff authority inventory fresh count price baseline actor < payoff authority inventory fresh count price candidate actor) ∨
    ((classify authority inventory fresh count price actor baseline).selected = none ∧
      paidWindow authority inventory fresh baseline = true ∧
      ∀ candidate ∈ menu authority inventory fresh, sameWindow authority inventory fresh count actor baseline candidate = true →
        financial authority inventory fresh count price baseline actor true - financial authority inventory fresh count price candidate actor true ≤
          budget authority inventory fresh count price baseline actor candidate - gains authority inventory fresh count price baseline actor candidate) := by
  cases result : classify authority inventory fresh count price actor baseline
  next denied => exact Or.inl ⟨denied,rfl⟩
  next candidate member =>
      have actual := every_computed_improvement_has_its_real_paid_window authority inventory fresh count price actor baseline candidate member
      exact Or.inr (Or.inl ⟨candidate,rfl,actual⟩)
  next paid checked =>
      refine Or.inr (Or.inr ⟨rfl,paid,?_⟩)
      intro candidate member window
      exact computed_stability_bounds_the_original_selected_net authority inventory fresh count price actor baseline checked candidate member window

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Appraisal
