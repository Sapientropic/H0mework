import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Resource

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Exit

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

inductive Method where
  | direct | productive | loan
  deriving DecidableEq

def production (actor : Bool) : Action := ⟨actor, [], .resource, [], .produce actor⟩
def principal (current : Current) (actor : Bool) := max 0 (1 - current.stock actor .service)

def Method.prefix (method : Method) (current : Current) (actor : Bool) : List Action :=
  match method with
  | .direct => []
  | .productive => [production actor]
  | .loan =>
    [⟨actor, [], .resource, [], .issue () actor (!actor) (principal current actor)⟩,
     ⟨!actor, [], .resource, [], .transfer (!actor) actor [(.service, principal current actor)]⟩]

def beforeExit (current : Current) (actor : Bool) (method : Method) :=
  (law.execute current 0 (method.prefix current actor)).final

def candidate (current : Current) (actor : Bool) (method : Method) :=
  signedWord (method.prefix current actor ++ [request scope (beforeExit current actor method) actor .exit])

def Legal (current : Current) (actor : Bool) (method : Method) : Prop :=
  ∀ item ∈ law.rawItems current (candidate current actor method), law.Valid item.before item.request

instance (current : Current) (actor : Bool) (method : Method) : Decidable (Legal current actor method) := by
  unfold Legal; infer_instance

def methods : List Method := [.direct, .productive, .loan]

structure Ready (current : Current) (actor : Bool) where
  private mk ::
  method : Method
  included : method ∈ methods
  legal : Legal current actor method

def choose (current : Current) (actor : Bool) : Option (Ready current actor) :=
  match found : methods.find? (fun method => decide (Legal current actor method)) with
  | some method => some ⟨method, List.mem_of_find?_eq_some found,
      of_decide_eq_true (List.find?_some (p := fun method => decide (Legal current actor method)) found)⟩
  | none => none

def selected (current : Current) (actor : Bool) : Method :=
  match choose current actor with | some ready => ready.method | none => .productive

def core (current : Current) (actor : Bool) := candidate current actor (selected current actor)

structure Demand (current : Current) (actor : Bool) where
  private mk ::
  item : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit
  actual : item ∈ law.rawItems current (core current actor)
  refused : ¬ law.Valid item.before item.request
  debit : (Bool × Good) × ℚ
  required : debit ∈ law.debit item.before item.request
  shortfall : 0 < debit.2 - item.before.stock debit.1.1 debit.1.2

def demands (current : Current) (actor : Bool) : List (Demand current actor) :=
  (law.rawItems current (core current actor)).attach.flatMap fun item =>
    if refused : ¬ law.Valid item.val.before item.val.request then
      (law.debit item.val.before item.val.request).attach.filterMap fun debit =>
        if shortfall : 0 < debit.val.2 - item.val.before.stock debit.val.1.1 debit.val.1.2 then
          some ⟨item.val, item.property, refused, debit.val, debit.property, shortfall⟩ else none
    else []

def Demand.quantity {current : Current} {actor : Bool} (demand : Demand current actor) :=
  demand.debit.2 - demand.item.before.stock demand.debit.1.1 demand.debit.1.2

def Demand.supplier {current : Current} {actor : Bool} (demand : Demand current actor) := !demand.debit.1.1

def Demand.request {current : Current} {actor : Bool} (demand : Demand current actor) : Action :=
  ⟨demand.supplier, [], .resource, [],
    .transfer demand.supplier demand.debit.1.1 [(demand.debit.1.2, demand.quantity)]⟩

def repairs (current : Current) (actor : Bool) := (demands current actor).map Demand.request

def word (current : Current) (actor : Bool) := core current actor ++ repairs current actor

theorem every_demand_is_a_positive_actual_refusal (current : Current) (actor : Bool) (demand : Demand current actor) :
    demand.item ∈ law.rawItems current (word current actor) ∧ ¬ law.Valid demand.item.before demand.item.request ∧
    demand.debit ∈ law.debit demand.item.before demand.item.request ∧ 0 < demand.quantity := by
  unfold word RawLaw.rawItems
  rw [law.execute_append]
  exact ⟨List.mem_append_left _ demand.actual, demand.refused, demand.required, demand.shortfall⟩

theorem every_positive_refusal_is_recorded (current : Current) (actor : Bool)
    (item : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit)
    (actual : item ∈ law.rawItems current (core current actor)) (refused : ¬ law.Valid item.before item.request)
    (debit : (Bool × Good) × ℚ) (required : debit ∈ law.debit item.before item.request)
    (shortfall : 0 < debit.2 - item.before.stock debit.1.1 debit.1.2) :
    ∃ demand ∈ demands current actor, demand.item = item ∧ demand.debit = debit := by
  refine ⟨⟨item, actual, refused, debit, required, shortfall⟩, ?_, rfl, rfl⟩
  apply List.mem_flatMap.mpr
  refine ⟨⟨item, actual⟩, List.mem_attach _ _, ?_⟩
  simp only [dif_pos refused]
  exact List.mem_filterMap.mpr ⟨⟨debit, required⟩, List.mem_attach _ _, by simp only [dif_pos shortfall]⟩

theorem paid_core_has_no_repair_suffix (current : Current) (actor : Bool) (ready : Ready current actor)
    (chosen : choose current actor = some ready) : word current actor = candidate current actor ready.method := by
  have exactCore : core current actor = candidate current actor ready.method := by simp only [core, selected, chosen]
  have noDemand : demands current actor = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro demand _
    exact demand.refused (ready.legal demand.item (exactCore ▸ demand.actual))
  simp only [word, repairs, noDemand, List.map_nil, List.append_nil, exactCore]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Exit
