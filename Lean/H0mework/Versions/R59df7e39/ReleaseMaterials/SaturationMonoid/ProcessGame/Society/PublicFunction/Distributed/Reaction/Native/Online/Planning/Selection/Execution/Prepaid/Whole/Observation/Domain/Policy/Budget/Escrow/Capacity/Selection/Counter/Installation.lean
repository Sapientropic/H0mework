import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Binding
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {units : Nat}

namespace Outcome
def family : Outcome prepared units → Prepared input
  | .unfunded (.empty _) => prepared
  | .unfunded (.refused funding ..) => funding.installed
  | .unavailable paid .. => paid.family
  | .exhausted made .. | .shortfall made .. => made.paid.family
  | .released made => made.programme.paid.family

theorem source_order_and_multiplicity (outcome : Outcome prepared units) :
    outcome.family.saved.map Cell.point = prepared.saved.map Cell.point := by
  cases outcome with
  | unfunded why => cases why with
    | empty => rfl
    | refused funding => exact funding.source_order_and_multiplicity
  | unavailable paid => exact paid.funding.source_order_and_multiplicity
  | exhausted made | shortfall made => exact made.paid.funding.source_order_and_multiplicity
  | released made => exact made.programme.paid.funding.source_order_and_multiplicity

def endpoint : (outcome : Outcome prepared units) → (index : Index outcome.family) →
    Binding.NativeCursor outcome.family.saved[index].point
  | .unfunded (.empty _),index => Protocol.retained prepared.saved[index].stage
  | .unfunded (.refused funding ..),index => Protocol.retained funding.installed.saved[index].stage
  | .unavailable paid ..,index => Protocol.retained paid.family.saved[index].stage
  | .exhausted made ..,index | .shortfall made ..,index => Protocol.retained made.paid.family.saved[index].stage
  | .released made,index => match made.work.outcome with
    | .selected choice => choice.endpoint index
    | .blocked _ => Protocol.retained made.programme.paid.family.saved[index].stage

theorem released_selection_executes_the_same_native_intent (made : Release prepared units)
    (choice : Choice made.programme.actual.pool) (selected : made.work.outcome = .selected choice)
    (index : Index made.programme.paid.family) :
    (Outcome.released made).endpoint index = choice.endpoint index := by
  simp only [endpoint,selected]

theorem blocked_selection_retains_the_actual_paid_prefix (made : Release prepared units)
    (rejected : ∀ policy : Section made.programme.actual.pool,Rejection made.programme.actual.pool policy)
    (blocked : made.work.outcome = .blocked rejected) (index : Index made.programme.paid.family) :
    (Outcome.released made).endpoint index = Protocol.retained made.programme.paid.family.saved[index].stage := by
  simp only [endpoint,blocked]
  rfl

theorem unavailable_retains_the_actual_paid_prefix (paid : PaidSelection.Funded prepared units)
    (source : SourceQuota.Generated paid.family) (why : PaidSelection.NoDomain source) (index : Index paid.family) :
    (Outcome.unavailable paid source why).endpoint index = Protocol.retained paid.family.saved[index].stage := rfl

theorem exhausted_retains_the_actual_paid_prefix (made : Programme prepared units) (state : Frame made.actual.pool)
    (same : made.calculation.run.endpoint = state) (spent : made.calculation.run.spent = units) (index : Index made.paid.family) :
    (Outcome.exhausted made state same spent).endpoint index = Protocol.retained made.paid.family.saved[index].stage := rfl
end Outcome

namespace Record
variable (made : Record prepared units)
abbrev family := made.outcome.family
abbrev endpoint (index : Index made.family) := made.outcome.endpoint index

def originalIndex (index : Index made.family) : Index prepared :=
  ⟨index.val,by
    have sizes : made.family.saved.length = prepared.saved.length := by
      simpa only [List.length_map] using congrArg List.length made.outcome.source_order_and_multiplicity
    exact sizes ▸ index.isLt⟩

theorem original_point (index : Index made.family) :
    prepared.saved[made.originalIndex index].point = made.family.saved[index].point := by
  have same := congrArg (fun xs : List (NativePoint input) => xs[index.val]?) made.outcome.source_order_and_multiplicity
  have bounded : index.val < prepared.saved.length := (made.originalIndex index).isLt
  simp only [List.getElem?_map,List.getElem?_eq_getElem index.isLt,
    List.getElem?_eq_getElem bounded,Option.map_some] at same
  exact (Option.some.inj same).symm

variable {point : NativePoint input} (bound : Binding.Linked made.family point)
def nativeEndpoint : Binding.NativeCursor point := bound.point_exact ▸ made.endpoint bound.index

theorem native_endpoint_is_the_same_actual_execution : HEq (made.endpoint bound.index) (made.nativeEndpoint bound) := by
  exact (@eqRec_heq (NativePoint input) (fun p => Binding.NativeCursor p) _ _ bound.point_exact (made.endpoint bound.index)).symm

theorem bound_origin_is_the_original_observed_point : prepared.saved[made.originalIndex bound.index].point = point :=
  (made.original_point bound.index).trans bound.point_exact

private theorem transport_input {first second : NativePoint input} (same : first = second)
    (cursor : Binding.NativeCursor first) :
    ((same ▸ cursor : Binding.NativeCursor second).source.val.input) = cursor.source.val.input := by
  cases same
  rfl

theorem original_root_input_survives_the_point_transport :
    (made.nativeEndpoint bound).source.val.input = (made.endpoint bound.index).source.val.input :=
  transport_input bound.point_exact _

end Record
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid
