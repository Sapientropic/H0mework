import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Resource

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

inductive Delivery {current : Current} (demand : Demand current) (before : Current) where
  | private paid (accepted : law.Valid before demand.request)
  | private blocked (refused : ¬ law.Valid before demand.request)
      (missing : before.stock demand.supplier demand.debit.1.2 < demand.quantity)
      (noOther : ∀ supplier : Bool, supplier ≠ demand.debit.1.1 → ¬ law.Valid before (demand.requestTo supplier))

def deliver {current : Current} (demand : Demand current) (before : Current) : Delivery demand before :=
  if accepted : law.Valid before demand.request then .paid accepted
  else .blocked accepted
    (lt_of_not_ge (fun funded => accepted ((supply_valid_iff_material demand before).mpr funded)))
    (demand.refusal_covers_all_distinct_suppliers before accepted)

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
  simp [RawLaw.paidStep, Demand.request, Demand.requestTo, RawLaw.debit, RawLaw.credit,
    locate, flowAt, amount, distinct]

theorem every_supply_has_a_paid_effect_or_a_material_obstruction {current : Current} (event : SupplyEvent current) :
    (law.Valid event.before event.demand.request ∧
      event.before.stock event.demand.debit.1.1 event.demand.debit.1.2 <
        event.after.stock event.demand.debit.1.1 event.demand.debit.1.2) ∨
    (¬ law.Valid event.before event.demand.request ∧ event.after = event.before ∧
      event.before.stock event.demand.supplier event.demand.debit.1.2 < event.demand.quantity ∧
      ∀ supplier : Bool, supplier ≠ event.demand.debit.1.1 → ¬ law.Valid event.before (event.demand.requestTo supplier)) := by
  cases event.delivery
  next accepted =>
      exact Or.inl ⟨accepted, by rw [paid_supply_is_a_real_stock_increase event accepted]; exact lt_add_of_pos_right _ event.demand.shortfall⟩
  next refused missing noOther =>
      exact Or.inr ⟨refused, law.rejected_preserves_current _ _ refused, missing, noOther⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening
