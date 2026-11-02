import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Exit.Effects

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Exit

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

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
    (present : event ∈ supplies current actor) : event.item ∈ law.rawItems current (word current actor) := by
  have actual : event.item ∈ (supplies current actor).map SupplyEvent.item := List.mem_map.mpr ⟨event, present, rfl⟩
  rw [supplies, supply_trace_is_the_actual_interpreter] at actual
  rw [word_is_its_core_and_repairs]
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

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Exit
