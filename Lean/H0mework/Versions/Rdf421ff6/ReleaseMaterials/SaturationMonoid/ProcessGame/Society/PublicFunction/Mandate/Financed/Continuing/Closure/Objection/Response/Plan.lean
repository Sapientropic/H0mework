import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Native

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Response

open Institutions.Capitalism.Universal.Source.Program

/-- A counterparty is read from the current authority, not supplied as an
already cooperative replacement. Its actual requests still face the law. -/
def counterparties (current : Current) : List Bool :=
  (current.technology.holder.toList ++ current.technology.offered.toList).filter (fun actor => actor != false)

inductive Method where
  | direct | productive | loan (lender : Bool)
  deriving DecidableEq

def production : Action := ⟨false, [], .resource, [], .produce false⟩

def principal (current : Current) : ℚ := max 0 (1 - current.stock false .service)

def terms (current : Current) (lender : Bool) : Financing.Terms Bool Unit :=
  ⟨false, lender, (), principal current⟩

def Method.prefix (current : Current) : Method → List Action
  | .direct => []
  | .productive => [production]
  | .loan lender =>
      [⟨false, [], .resource, [], .issue () false lender (principal current)⟩,
       ⟨lender, [], .resource, [], .transfer lender false [(.service, principal current)]⟩]

def Method.word (current : Current) (method : Method) : List Action :=
  method.prefix current ++ [request scope (law.execute current 0 (method.prefix current)).final false .revoke]

def methods (current : Current) : List Method := [.direct, .productive] ++ if 0 < principal current then (counterparties current).map Method.loan else []

def Legal (current : Current) (method : Method) : Prop :=
  ∀ item ∈ law.rawItems current (method.word current), law.Valid item.before item.request

instance (current : Current) (method : Method) : Decidable (Legal current method) := by unfold Legal; infer_instance

structure Ready (current : Current) where
  private mk ::
  method : Method
  original : method ∈ methods current
  accepted : Legal current method

def choose (current : Current) : Option (Ready current) :=
  (methods current).attach.findSome? fun method =>
    if accepted : Legal current method.val then some ⟨method.val, method.property, accepted⟩ else none

def core (current : Current) : List Action :=
  match choose current with | some ready => ready.method.word current | none => Method.productive.word current

structure Failure (current : Current) where
  private mk ::
  item : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit
  original : item ∈ law.rawItems current (core current)
  refused : ¬ law.Valid item.before item.request

def failures (current : Current) : List (Failure current) :=
  (law.rawItems current (core current)).attach.filterMap fun item =>
    if refused : ¬ law.Valid item.val.before item.val.request then some ⟨item.val, item.property, refused⟩ else none

structure Order (current : Current) where
  private mk ::
  failure : Failure current
  debit : (Bool × Good) × ℚ
  required : debit ∈ law.debit failure.item.before failure.item.request
  shortfall : 0 < debit.2 - failure.item.before.stock debit.1.1 debit.1.2
  supplier : Bool
  participant : supplier ∈ counterparties current
  distinct : supplier ≠ debit.1.1

def orders (current : Current) : List (Order current) :=
  (failures current).flatMap fun failure =>
    (law.debit failure.item.before failure.item.request).attach.flatMap fun debit =>
      if shortfall : 0 < debit.val.2 - failure.item.before.stock debit.val.1.1 debit.val.1.2 then
        ((counterparties current).filter (fun supplier => decide (supplier ≠ debit.val.1.1))).attach.map fun supplier =>
          ⟨failure, debit.val, debit.property, shortfall, supplier.val,
            (List.mem_filter.mp supplier.property).1, by
              have selected : decide (supplier.val ≠ debit.val.1.1) = true := (List.mem_filter.mp supplier.property).2
              exact of_decide_eq_true selected⟩
      else []

def Order.request {current : Current} (order : Order current) : Action :=
  let after := (law.execute current 0 (core current)).final
  ⟨order.supplier, [], law.stockPort after.technology order.supplier order.debit.1.2, [],
    .transfer order.supplier order.debit.1.1
      [(order.debit.1.2, order.debit.2 - order.failure.item.before.stock order.debit.1.1 order.debit.1.2)]⟩

def word (current : Current) : List Action := core current ++ (orders current).map Order.request

def funding (current : Current) : Option (Sigma fun lender : Bool =>
    Financing.Disbursement law current (word current) (terms current lender)) :=
  match choose current with
  | some ready => match ready.method with
      | .loan lender => (Financing.readDisbursement? law current (word current) (terms current lender)).map (fun receipt => ⟨lender, receipt⟩)
      | _ => none
  | none => none

theorem every_failure_is_in_the_actual_word (current : Current) (failure : Failure current) :
    failure.item ∈ law.rawItems current (word current) ∧ ¬ law.Valid failure.item.before failure.item.request := by
  unfold word RawLaw.rawItems
  rw [law.execute_append]
  exact ⟨List.mem_append_left _ failure.original, failure.refused⟩

theorem every_order_is_an_actual_request (current : Current) (order : Order current) (present : order ∈ orders current) :
    order.request ∈ word current :=
  List.mem_append_right _ (List.mem_map.mpr ⟨order, present, rfl⟩)

theorem word_contains_its_own_revoke (current : Current) :
    ∃ item ∈ law.rawItems current (word current), isRevoke item.before item.request = true := by
  let method := match choose current with | some ready => ready.method | none => .productive
  have exactCore : core current = method.word current := by unfold core method; split <;> rfl
  let before := (law.execute current 0 (method.prefix current)).final
  let item : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit :=
    ⟨(method.prefix current).length, before, request scope before false .revoke⟩
  refine ⟨item, ?_, (isRevoke_iff _ _).mpr rfl⟩
  unfold word
  rw [exactCore]
  unfold Method.word RawLaw.rawItems
  rw [law.execute_append, law.execute_append]
  apply List.mem_append_left
  apply List.mem_append_right
  simp only [RawLaw.execute, List.mem_cons, List.not_mem_nil, or_false]
  simp only [item, before, Nat.zero_add]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Response
