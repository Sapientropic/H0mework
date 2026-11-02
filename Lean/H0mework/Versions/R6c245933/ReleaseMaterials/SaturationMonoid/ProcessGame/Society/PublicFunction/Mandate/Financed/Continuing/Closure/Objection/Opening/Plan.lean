import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Signature

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

abbrev Method := Response.Method

def methods : List Method := [.direct, .productive, .loan true]

def candidate (current : Current) (method : Method) : List Action :=
  signedWord (method.word (law.step current submission))

def Legal (current : Current) (method : Method) : Prop :=
  ∀ item ∈ law.rawItems current (candidate current method), law.Valid item.before item.request

instance (current : Current) (method : Method) : Decidable (Legal current method) := by unfold Legal; infer_instance

inductive Selection (current : Current) where
  | private paid (method : Method) (included : method ∈ methods) (legal : Legal current method)
  | private blocked (refused : ∀ method ∈ methods, ¬ Legal current method)

def select (current : Current) : Selection current :=
  match selected : methods.find? (fun method => decide (Legal current method)) with
  | some method => .paid method (List.mem_of_find?_eq_some selected)
      (of_decide_eq_true (List.find?_some (p := fun method => decide (Legal current method)) selected))
  | none => .blocked (by
      intro method included legal
      have denied := List.find?_eq_none.mp selected method included
      have accepted : decide (Legal current method) = true := decide_eq_true legal
      rw [accepted] at denied
      exact denied rfl)

def Selection.method {current : Current} : Selection current → Method
  | .paid method .. => method
  | .blocked .. => .productive

def core (current : Current) := candidate current (select current).method

structure Refusal (current : Current) where
  private mk ::
  item : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit
  actual : item ∈ law.rawItems current (core current)
  refused : ¬ law.Valid item.before item.request

def refusals (current : Current) : List (Refusal current) :=
  (law.rawItems current (core current)).attach.filterMap fun item =>
    if refused : ¬ law.Valid item.val.before item.val.request then some ⟨item.val, item.property, refused⟩ else none

structure Demand (current : Current) where
  private mk ::
  refusal : Refusal current
  debit : (Bool × Good) × ℚ
  required : debit ∈ law.debit refusal.item.before refusal.item.request
  shortfall : 0 < debit.2 - refusal.item.before.stock debit.1.1 debit.1.2

def gaps (current : Current) : List (Demand current) :=
  (refusals current).flatMap fun refusal =>
    (law.debit refusal.item.before refusal.item.request).attach.filterMap fun debit =>
      if shortfall : 0 < debit.val.2 - refusal.item.before.stock debit.val.1.1 debit.val.1.2 then
        some ⟨refusal, debit.val, debit.property, shortfall⟩ else none

theorem every_actual_refusal_is_recorded (current : Current)
    (item : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit)
    (actual : item ∈ law.rawItems current (core current)) (refused : ¬ law.Valid item.before item.request) :
    ∃ refusal ∈ refusals current, refusal.item = item := by
  refine ⟨⟨item, actual, refused⟩, ?_, rfl⟩
  apply List.mem_filterMap.mpr
  refine ⟨⟨item, actual⟩, List.mem_attach _ _, ?_⟩
  simp only [dif_pos refused]

theorem every_positive_gap_is_recorded (current : Current) (refusal : Refusal current)
    (present : refusal ∈ refusals current) (debit : (Bool × Good) × ℚ)
    (required : debit ∈ law.debit refusal.item.before refusal.item.request)
    (shortfall : 0 < debit.2 - refusal.item.before.stock debit.1.1 debit.1.2) :
    ∃ demand ∈ gaps current, demand.refusal = refusal ∧ demand.debit = debit := by
  refine ⟨⟨refusal, debit, required, shortfall⟩, ?_, rfl, rfl⟩
  apply List.mem_flatMap.mpr
  refine ⟨refusal, present, ?_⟩
  apply List.mem_filterMap.mpr
  exact ⟨⟨debit, required⟩, List.mem_attach _ _, by simp only [dif_pos shortfall]⟩

def demands (current : Current) : List (Demand current) :=
  match select current with
  | .paid .. => []
  | .blocked .. => gaps current

def Demand.quantity {current : Current} (demand : Demand current) :=
  demand.debit.2 - demand.refusal.item.before.stock demand.debit.1.1 demand.debit.1.2

/-- The other address is generated from this unpaid debit. Its signature is
only a submitted request; the actual law still decides whether it pays. -/
def Demand.requestTo {current : Current} (demand : Demand current) (supplier : Bool) : Action :=
  ⟨supplier, [], .resource, [], .transfer supplier demand.debit.1.1 [(demand.debit.1.2, demand.quantity)]⟩

def Demand.supplier {current : Current} (demand : Demand current) := !demand.debit.1.1

def Demand.request {current : Current} (demand : Demand current) := demand.requestTo demand.supplier

def repairs (current : Current) := (demands current).map Demand.request

def suffix (current : Current) :=
  (select current).method.word (law.step current submission) ++ repairs current

def word (current : Current) := signedWord (suffix current)

private theorem signedWord_append (left right : List Action) :
    signedWord (left ++ right) = signedWord left ++ right := by
  simp only [signedWord, List.cons_append]

theorem word_is_its_core_and_repairs (current : Current) : word current = core current ++ repairs current := by
  unfold word suffix core candidate
  exact signedWord_append _ _

def Selection.isPaid {current : Current} : Selection current → Bool
  | .paid .. => true
  | .blocked .. => false

theorem a_paid_plan_has_no_unpaid_repair_suffix (current : Current)
    (paid : (select current).isPaid = true) : word current = candidate current (select current).method := by
  unfold word suffix repairs demands
  generalize chosen : select current = selection at paid ⊢
  cases selection
  next method included legal =>
      simp only [List.map_nil, List.append_nil, Selection.method]
      rfl
  next refused => cases paid

theorem every_refusal_is_in_the_actual_word (current : Current) (refusal : Refusal current) :
    refusal.item ∈ law.rawItems current (word current) ∧ ¬ law.Valid refusal.item.before refusal.item.request := by
  rw [word_is_its_core_and_repairs]
  unfold RawLaw.rawItems
  rw [law.execute_append]
  exact ⟨List.mem_append_left _ refusal.actual, refusal.refused⟩

theorem every_demand_is_a_positive_original_debit (current : Current) (demand : Demand current) :
    demand.refusal.item ∈ law.rawItems current (word current) ∧
    demand.debit ∈ law.debit demand.refusal.item.before demand.refusal.item.request ∧ 0 < demand.quantity :=
  ⟨(every_refusal_is_in_the_actual_word current demand.refusal).1, demand.required, demand.shortfall⟩

theorem every_demand_generates_an_actual_request (current : Current) (demand : Demand current)
    (included : demand ∈ demands current) : demand.request ∈ word current := by
  rw [word_is_its_core_and_repairs]
  exact List.mem_append_right _ (List.mem_map.mpr ⟨demand, included, rfl⟩)

theorem Demand.supplier_is_distinct {current : Current} (demand : Demand current) : demand.supplier ≠ demand.debit.1.1 := by
  cases same : demand.debit.1.1 <;> simp_all [Demand.supplier]

theorem Demand.every_distinct_supplier_is_this_address {current : Current} (demand : Demand current) (supplier : Bool)
    (distinct : supplier ≠ demand.debit.1.1) : supplier = demand.supplier := by
  cases supplier <;> cases same : demand.debit.1.1 <;> simp_all [Demand.supplier]

theorem Demand.refusal_covers_all_distinct_suppliers {current : Current} (demand : Demand current) (before : Current)
    (refused : ¬ law.Valid before demand.request) :
    ∀ supplier : Bool, supplier ≠ demand.debit.1.1 → ¬ law.Valid before (demand.requestTo supplier) := by
  intro supplier distinct
  rw [demand.every_distinct_supplier_is_this_address supplier distinct]
  exact refused

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening
