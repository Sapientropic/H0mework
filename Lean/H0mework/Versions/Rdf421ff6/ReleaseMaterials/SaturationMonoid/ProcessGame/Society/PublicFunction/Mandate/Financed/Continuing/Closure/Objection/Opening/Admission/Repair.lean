import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Admission.Grant

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Admission

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

structure Demand (current : Current) where
  private mk ::
  item : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit
  actual : item ∈ law.rawItems current (core current)
  refused : ¬ law.Valid item.before item.request
  permitted : law.operationAllowed item.before item.request = true
  debit : (Bool × Good) × ℚ
  required : debit ∈ law.debit item.before item.request
  shortfall : 0 < debit.2 - item.before.stock debit.1.1 debit.1.2

def demands (current : Current) : List (Demand current) :=
  (law.rawItems current (core current)).attach.flatMap fun item =>
    if permitted : law.operationAllowed item.val.before item.val.request = true then
      if refused : ¬ law.Valid item.val.before item.val.request then
        (law.debit item.val.before item.val.request).attach.filterMap fun debit =>
          if shortfall : 0 < debit.val.2 - item.val.before.stock debit.val.1.1 debit.val.1.2 then
            some ⟨item.val, item.property, refused, permitted, debit.val, debit.property, shortfall⟩ else none
      else []
    else []

def Demand.quantity {current : Current} (demand : Demand current) :=
  demand.debit.2 - demand.item.before.stock demand.debit.1.1 demand.debit.1.2

def Demand.supplier {current : Current} (demand : Demand current) := !demand.debit.1.1

def Demand.request {current : Current} (demand : Demand current) : Action :=
  ⟨demand.supplier, [], .resource, [],
    .transfer demand.supplier demand.debit.1.1 [(demand.debit.1.2, demand.quantity)]⟩

def repairs (current : Current) := (demands current).map Demand.request

def word (current : Current) := core current ++ repairs current

theorem every_demand_is_a_positive_actual_refusal (current : Current) (demand : Demand current) :
    demand.item ∈ law.rawItems current (word current) ∧ ¬ law.Valid demand.item.before demand.item.request ∧
    demand.debit ∈ law.debit demand.item.before demand.item.request ∧ 0 < demand.quantity := by
  unfold word RawLaw.rawItems
  rw [law.execute_append]
  exact ⟨List.mem_append_left _ demand.actual, demand.refused, demand.required, demand.shortfall⟩

theorem every_positive_refusal_is_recorded (current : Current)
    (item : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit)
    (actual : item ∈ law.rawItems current (core current)) (refused : ¬ law.Valid item.before item.request)
    (permitted : law.operationAllowed item.before item.request = true)
    (debit : (Bool × Good) × ℚ) (required : debit ∈ law.debit item.before item.request)
    (shortfall : 0 < debit.2 - item.before.stock debit.1.1 debit.1.2) :
    ∃ demand ∈ demands current, demand.item = item ∧ demand.debit = debit := by
  refine ⟨⟨item, actual, refused, permitted, debit, required, shortfall⟩, ?_, rfl, rfl⟩
  apply List.mem_flatMap.mpr
  refine ⟨⟨item, actual⟩, List.mem_attach _ _, ?_⟩
  simp only [dif_pos permitted, dif_pos refused]
  exact List.mem_filterMap.mpr ⟨⟨debit, required⟩, List.mem_attach _ _, by simp only [dif_pos shortfall]⟩

theorem paid_word_is_the_selected_pair (current : Current) (ready : Ready current)
    (chosen : choose current = some ready) : word current = candidate current ready.choice := by
  have exactCore : core current = candidate current ready.choice := by simp only [core, selected, chosen]
  have noDemand : demands current = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro demand _
    exact demand.refused (ready.legal demand.item (exactCore ▸ demand.actual))
  simp only [word, repairs, noDemand, List.map_nil, List.append_nil, exactCore]

inductive FailedGuard (item : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit) : Prop where
  | private signer (denied : ¬ RawLaw.SignerMatches item.request)
  | private policy (denied : ¬ law.operationAllowed item.before item.request = true)
  | private permission (denied : ¬ ∀ port ∈ law.requiredPorts item.before item.request,
      law.allowed item.before.technology port item.request.signer = true ∨ law.controller item.before.technology port ∈ item.request.consents)
  | private claim (denied : ¬ law.ClaimGuard item.before item.request)
  | private debit (denied : ¬ NonnegativeBundle (Bool × Good) (law.debit item.before item.request))
  | private credit (denied : ¬ NonnegativeBundle (Bool × Good) (law.credit item.before item.request))
  | private stock (denied : ¬ ∀ entry ∈ law.debit item.before item.request,
      flowAt (law.debit item.before item.request) entry.1.1 entry.1.2 ≤ item.before.stock entry.1.1 entry.1.2)

theorem failedGuard (item : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit)
    (refused : ¬ law.Valid item.before item.request) : FailedGuard item := by
  if signer : RawLaw.SignerMatches item.request then
    if policy : law.operationAllowed item.before item.request = true then
      if permission : ∀ port ∈ law.requiredPorts item.before item.request,
          law.allowed item.before.technology port item.request.signer = true ∨ law.controller item.before.technology port ∈ item.request.consents then
        if claim : law.ClaimGuard item.before item.request then
          if debit : NonnegativeBundle (Bool × Good) (law.debit item.before item.request) then
            if credit : NonnegativeBundle (Bool × Good) (law.credit item.before item.request) then
              exact .stock (fun stock => refused ⟨⟨signer, policy⟩, permission, claim, debit, credit, stock⟩)
            else exact .credit credit
          else exact .debit debit
        else exact .claim claim
      else exact .permission permission
    else exact .policy policy
  else exact .signer signer

structure Refusal (current : Current) where
  private mk ::
  item : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit
  actual : item ∈ law.rawItems current (core current)
  refused : ¬ law.Valid item.before item.request
  reason : FailedGuard item

def refusals (current : Current) : List (Refusal current) :=
  (law.rawItems current (core current)).attach.filterMap fun item =>
    if refused : ¬ law.Valid item.val.before item.val.request then
      some ⟨item.val, item.property, refused, failedGuard item.val refused⟩ else none

theorem every_blocked_core_retains_an_actual_guard_failure (current : Current) (blocked : choose current = none) :
    ∃ refusal, refusal ∈ refusals current := by
  obtain ⟨item, actual, refused⟩ := blocked_core_has_a_real_refusal current blocked
  refine ⟨⟨item, actual, refused, failedGuard item refused⟩, ?_⟩
  exact List.mem_filterMap.mpr ⟨⟨item, actual⟩, List.mem_attach _ _, by simp only [dif_pos refused]⟩

theorem a_policy_refusal_is_not_disguised_as_material_repair (current : Current)
    (item : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit)
    (denied : law.operationAllowed item.before item.request = false) (demand : Demand current) : demand.item ≠ item := by
  intro same
  have permitted := demand.permitted
  rw [same, denied] at permitted
  cases permitted

theorem Demand.supplier_is_distinct {current : Current} (demand : Demand current) :
    demand.supplier ≠ demand.debit.1.1 := by
  cases same : demand.debit.1.1 <;> simp_all [Demand.supplier]

theorem supply_valid_iff_material {current : Current} (demand : Demand current) (before : Current) :
    law.Valid before demand.request ↔ demand.quantity ≤ before.stock demand.supplier demand.debit.1.2 := by
  have positive := le_of_lt demand.shortfall
  simp [law, Mandate.law, Demand.request, RawLaw.Valid, RawLaw.SignerMatches,
    RawLaw.operationAllowed, RawPolicy.eval, RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit,
    RawLaw.ClaimGuard, eraseCurrent, eraseRequest, eraseOperation, TaskUse, base, scope, task,
    Delegation.members, NonnegativeBundle, locate, flowAt, amount, positive, Demand.quantity]

theorem word_is_its_core_and_repairs (current : Current) : word current = core current ++ repairs current := rfl

inductive Delivery {current : Current} (demand : Demand current) (before : Current) where
  | private paid (accepted : law.Valid before demand.request)
  | private blocked (refused : ¬ law.Valid before demand.request)
      (missing : before.stock demand.supplier demand.debit.1.2 < demand.quantity)


def deliver {current : Current} (demand : Demand current) (before : Current) : Delivery demand before :=
  if accepted : law.Valid before demand.request then .paid accepted
  else .blocked accepted
    (lt_of_not_ge (fun funded => accepted ((supply_valid_iff_material demand before).mpr funded)))


structure SupplyEvent (current : Current) where
  private mk ::
  demand : Demand current
  before : Current
  index : Nat
  delivery : Delivery demand before

def SupplyEvent.item {current : Current} (event : SupplyEvent current) :
    ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit :=
  ⟨event.index, event.before, event.demand.request⟩

def SupplyEvent.after {current : Current} (event : SupplyEvent current) := law.step event.before event.demand.request

def supplyTrace {current : Current} (before : Current) (index : Nat) : List (Demand current) → List (SupplyEvent current)
  | [] => []
  | demand :: tail => ⟨demand, before, index, deliver demand before⟩ ::
      supplyTrace (law.step before demand.request) (index + 1) tail

theorem supply_trace_is_the_actual_interpreter {current : Current} (before : Current) (index : Nat)
    (demands : List (Demand current)) :
    (supplyTrace before index demands).map SupplyEvent.item =
      (law.execute before index (demands.map Demand.request)).items := by
  induction demands generalizing before index with
  | nil => rfl
  | cons demand tail ih =>
      simp only [supplyTrace, List.map_cons, RawLaw.execute]
      rw [ih]
      rfl

theorem supply_trace_keeps_every_original_demand {current : Current} (before : Current) (index : Nat)
    (demands : List (Demand current)) : (supplyTrace before index demands).map SupplyEvent.demand = demands := by
  induction demands generalizing before index with
  | nil => rfl
  | cons demand tail ih => exact congrArg (List.cons demand) (ih (law.step before demand.request) (index + 1))

def supplies (current : Current) := supplyTrace (law.execute current 0 (core current)).final (core current).length (demands current)

theorem every_supply_is_in_the_original_word (current : Current) (event : SupplyEvent current)
    (present : event ∈ supplies current) : event.item ∈ law.rawItems current (word current) := by
  have actual : event.item ∈ (supplies current).map SupplyEvent.item := List.mem_map.mpr ⟨event, present, rfl⟩
  rw [supplies, supply_trace_is_the_actual_interpreter] at actual
  rw [word_is_its_core_and_repairs]
  unfold RawLaw.rawItems
  rw [law.execute_append]
  apply List.mem_append_right
  simpa only [Nat.zero_add, repairs] using actual

theorem every_supply_keeps_its_original_gap (current : Current) (event : SupplyEvent current)
    (present : event ∈ supplies current) : event.demand ∈ demands current := by
  have original : event.demand ∈ (supplies current).map SupplyEvent.demand := List.mem_map.mpr ⟨event, present, rfl⟩
  rwa [supplies, supply_trace_keeps_every_original_demand] at original

theorem paid_supply_is_a_real_stock_increase {current : Current} (event : SupplyEvent current)
    (accepted : law.Valid event.before event.demand.request) :
    event.after.stock event.demand.debit.1.1 event.demand.debit.1.2 =
      event.before.stock event.demand.debit.1.1 event.demand.debit.1.2 + event.demand.quantity := by
  have distinct := event.demand.supplier_is_distinct
  unfold SupplyEvent.after
  rw [RawLaw.step, if_pos accepted]
  simp [RawLaw.paidStep, Demand.request, RawLaw.debit, RawLaw.credit,
    locate, flowAt, amount, distinct]

theorem every_supply_has_a_paid_effect_or_a_material_obstruction {current : Current} (event : SupplyEvent current) :
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

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Admission
