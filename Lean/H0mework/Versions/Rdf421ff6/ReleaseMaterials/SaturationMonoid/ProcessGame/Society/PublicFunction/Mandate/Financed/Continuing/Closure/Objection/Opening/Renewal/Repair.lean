import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Renewal.Effects

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Renewal

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

structure Demand (current : Current) (actor : Bool) where
  private mk ::
  item : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit
  actual : item ∈ law.rawItems current (core current actor)
  refused : ¬ law.Valid item.before item.request
  permitted : law.operationAllowed item.before item.request = true
  debit : (Bool × Good) × ℚ
  required : debit ∈ law.debit item.before item.request
  shortfall : 0 < debit.2 - item.before.stock debit.1.1 debit.1.2

def demands (current : Current) (actor : Bool) : List (Demand current actor) :=
  (law.rawItems current (core current actor)).attach.flatMap fun item =>
    if permitted : law.operationAllowed item.val.before item.val.request = true then
      if refused : ¬ law.Valid item.val.before item.val.request then
        (law.debit item.val.before item.val.request).attach.filterMap fun debit =>
          if shortfall : 0 < debit.val.2 - item.val.before.stock debit.val.1.1 debit.val.1.2 then
            some ⟨item.val, item.property, refused, permitted, debit.val, debit.property, shortfall⟩ else none
      else []
    else []

def Demand.quantity {current : Current} {actor : Bool} (demand : Demand current actor) :=
  demand.debit.2 - demand.item.before.stock demand.debit.1.1 demand.debit.1.2

def Demand.supplier {current : Current} {actor : Bool} (demand : Demand current actor) := !demand.debit.1.1

def Demand.request {current : Current} {actor : Bool} (demand : Demand current actor) : Action :=
  ⟨demand.supplier, [], .resource, [],
    .transfer demand.supplier demand.debit.1.1 [(demand.debit.1.2, demand.quantity)]⟩

def repairs (current : Current) (actor : Bool) := (demands current actor).map Demand.request

def attemptedWord (current : Current) (actor : Bool) := core current actor ++ repairs current actor

theorem every_demand_is_a_positive_actual_refusal (current : Current) (actor : Bool) (demand : Demand current actor) :
    demand.item ∈ law.rawItems current (attemptedWord current actor) ∧ ¬ law.Valid demand.item.before demand.item.request ∧
    demand.debit ∈ law.debit demand.item.before demand.item.request ∧ 0 < demand.quantity := by
  unfold attemptedWord RawLaw.rawItems
  rw [law.execute_append]
  exact ⟨List.mem_append_left _ demand.actual, demand.refused, demand.required, demand.shortfall⟩

theorem every_positive_refusal_is_recorded (current : Current) (actor : Bool)
    (item : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit)
    (actual : item ∈ law.rawItems current (core current actor)) (refused : ¬ law.Valid item.before item.request)
    (permitted : law.operationAllowed item.before item.request = true)
    (debit : (Bool × Good) × ℚ) (required : debit ∈ law.debit item.before item.request)
    (shortfall : 0 < debit.2 - item.before.stock debit.1.1 debit.1.2) :
    ∃ demand ∈ demands current actor, demand.item = item ∧ demand.debit = debit := by
  refine ⟨⟨item, actual, refused, permitted, debit, required, shortfall⟩, ?_, rfl, rfl⟩
  apply List.mem_flatMap.mpr
  refine ⟨⟨item, actual⟩, List.mem_attach _ _, ?_⟩
  simp only [dif_pos permitted, dif_pos refused]
  exact List.mem_filterMap.mpr ⟨⟨debit, required⟩, List.mem_attach _ _, by simp only [dif_pos shortfall]⟩

theorem paid_prefix_is_the_selected_pair (current : Current) (actor : Bool) (ready : Ready current actor)
    (chosen : choose current actor = some ready) : attemptedWord current actor = candidate current actor ready.method := by
  have exactCore : core current actor = candidate current actor ready.method := by simp only [core, selected, chosen]
  have noDemand : demands current actor = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro demand _
    exact demand.refused (ready.legal demand.item (exactCore ▸ demand.actual))
  simp only [attemptedWord, repairs, noDemand, List.map_nil, List.append_nil, exactCore]

abbrev FailedGuard := Admission.FailedGuard

abbrev failedGuard := Admission.failedGuard

structure Refusal (current : Current) (actor : Bool) where
  private mk ::
  item : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit
  actual : item ∈ law.rawItems current (core current actor)
  refused : ¬ law.Valid item.before item.request
  reason : FailedGuard item

def refusals (current : Current) (actor : Bool) : List (Refusal current actor) :=
  (law.rawItems current (core current actor)).attach.filterMap fun item =>
    if refused : ¬ law.Valid item.val.before item.val.request then
      some ⟨item.val, item.property, refused, failedGuard item.val refused⟩ else none

theorem every_blocked_core_retains_an_actual_guard_failure (current : Current) (actor : Bool) (blocked : choose current actor = none) :
    ∃ refusal, refusal ∈ refusals current actor := by
  obtain ⟨item, actual, refused⟩ := blocked_core_has_a_real_refusal current actor blocked
  refine ⟨⟨item, actual, refused, failedGuard item refused⟩, ?_⟩
  exact List.mem_filterMap.mpr ⟨⟨item, actual⟩, List.mem_attach _ _, by simp only [dif_pos refused]⟩

theorem a_policy_refusal_is_not_disguised_as_material_repair (current : Current) (actor : Bool)
    (item : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit)
    (denied : law.operationAllowed item.before item.request = false) (demand : Demand current actor) : demand.item ≠ item := by
  intro same
  have permitted := demand.permitted
  rw [same, denied] at permitted
  cases permitted

theorem Demand.supplier_is_distinct {current : Current} {actor : Bool} (demand : Demand current actor) :
    demand.supplier ≠ demand.debit.1.1 := by
  cases same : demand.debit.1.1 <;> simp_all [Demand.supplier]

theorem supply_valid_iff_material {current : Current} {actor : Bool} (demand : Demand current actor) (before : Current) :
    law.Valid before demand.request ↔ demand.quantity ≤ before.stock demand.supplier demand.debit.1.2 := by
  have positive := le_of_lt demand.shortfall
  simp [law, Mandate.law, Demand.request, RawLaw.Valid, RawLaw.SignerMatches,
    RawLaw.operationAllowed, RawPolicy.eval, RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit,
    RawLaw.ClaimGuard, eraseCurrent, eraseRequest, eraseOperation, TaskUse, base, scope, task,
    Delegation.members, NonnegativeBundle, locate, flowAt, amount, positive, Demand.quantity]

theorem prefix_is_its_core_and_repairs (current : Current) (actor : Bool) : attemptedWord current actor = core current actor ++ repairs current actor := rfl

inductive Delivery {current : Current} {actor : Bool} (demand : Demand current actor) (before : Current) where
  | private paid (accepted : law.Valid before demand.request)
  | private blocked (refused : ¬ law.Valid before demand.request)
      (missing : before.stock demand.supplier demand.debit.1.2 < demand.quantity)


def deliver {current : Current} {actor : Bool} (demand : Demand current actor) (before : Current) : Delivery demand before :=
  if accepted : law.Valid before demand.request then .paid accepted
  else .blocked accepted
    (lt_of_not_ge (fun funded => accepted ((supply_valid_iff_material demand before).mpr funded)))


structure SupplyEvent (current : Current) (actor : Bool) where
  private mk ::
  demand : Demand current actor
  before : Current
  index : Nat
  delivery : Delivery demand before

def SupplyEvent.item {current : Current} {actor : Bool} (event : SupplyEvent current actor) :
    ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit :=
  ⟨event.index, event.before, event.demand.request⟩

def SupplyEvent.after {current : Current} {actor : Bool} (event : SupplyEvent current actor) := law.step event.before event.demand.request

def supplyTrace {current : Current} {actor : Bool} (before : Current) (index : Nat) : List (Demand current actor) → List (SupplyEvent current actor)
  | [] => []
  | demand :: tail => ⟨demand, before, index, deliver demand before⟩ ::
      supplyTrace (law.step before demand.request) (index + 1) tail

theorem supply_trace_is_the_actual_interpreter {current : Current} {actor : Bool} (before : Current) (index : Nat)
    (demands : List (Demand current actor)) :
    (supplyTrace before index demands).map SupplyEvent.item =
      (law.execute before index (demands.map Demand.request)).items := by
  induction demands generalizing before index with
  | nil => rfl
  | cons demand tail ih =>
      simp only [supplyTrace, List.map_cons, RawLaw.execute]
      rw [ih]
      rfl

theorem supply_trace_keeps_every_original_demand {current : Current} {actor : Bool} (before : Current) (index : Nat)
    (demands : List (Demand current actor)) : (supplyTrace before index demands).map SupplyEvent.demand = demands := by
  induction demands generalizing before index with
  | nil => rfl
  | cons demand tail ih => exact congrArg (List.cons demand) (ih (law.step before demand.request) (index + 1))

def supplies (current : Current) (actor : Bool) := supplyTrace (law.execute current 0 (core current actor)).final (core current actor).length (demands current actor)

theorem every_supply_is_in_the_original_word (current : Current) (actor : Bool) (event : SupplyEvent current actor)
    (present : event ∈ supplies current actor) : event.item ∈ law.rawItems current (attemptedWord current actor) := by
  have actual : event.item ∈ (supplies current actor).map SupplyEvent.item := List.mem_map.mpr ⟨event, present, rfl⟩
  rw [supplies, supply_trace_is_the_actual_interpreter] at actual
  rw [prefix_is_its_core_and_repairs]
  unfold RawLaw.rawItems
  rw [law.execute_append]
  apply List.mem_append_right
  simpa only [Nat.zero_add, repairs] using actual

theorem every_supply_keeps_its_original_gap (current : Current) (actor : Bool) (event : SupplyEvent current actor)
    (present : event ∈ supplies current actor) : event.demand ∈ demands current actor := by
  have original : event.demand ∈ (supplies current actor).map SupplyEvent.demand := List.mem_map.mpr ⟨event, present, rfl⟩
  rwa [supplies, supply_trace_keeps_every_original_demand] at original

theorem paid_supply_is_a_real_stock_increase {current : Current} {actor : Bool} (event : SupplyEvent current actor)
    (accepted : law.Valid event.before event.demand.request) :
    event.after.stock event.demand.debit.1.1 event.demand.debit.1.2 =
      event.before.stock event.demand.debit.1.1 event.demand.debit.1.2 + event.demand.quantity := by
  have distinct := event.demand.supplier_is_distinct
  unfold SupplyEvent.after
  rw [RawLaw.step, if_pos accepted]
  simp [RawLaw.paidStep, Demand.request, RawLaw.debit, RawLaw.credit,
    locate, flowAt, amount, distinct]

theorem every_supply_has_a_paid_effect_or_a_material_obstruction {current : Current} {actor : Bool} (event : SupplyEvent current actor) :
    (law.Valid event.before event.demand.request ∧
      event.before.stock event.demand.debit.1.1 event.demand.debit.1.2 <
        event.after.stock event.demand.debit.1.1 event.demand.debit.1.2) ∨
    (¬ law.Valid event.before event.demand.request ∧ event.after = event.before ∧
      event.before.stock event.demand.supplier event.demand.debit.1.2 < event.demand.quantity ) := by
  cases event.delivery
  next accepted =>
      exact Or.inl ⟨accepted, by rw [paid_supply_is_a_real_stock_increase event accepted]; exact lt_add_of_pos_right _ event.demand.shortfall⟩
  next refused missing =>
      exact Or.inr ⟨refused, law.rejected_preserves_current _ _ refused, missing⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Renewal
