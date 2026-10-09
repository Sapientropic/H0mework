import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Native.Frame.Stock.Return
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePolicyQueryTraceReturnControls
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations CofinalHistorySettlement
namespace R
export SourceOperationInquiry.Context.Native.Frame.Stock.Return
 (written eventReceipt new_event_born new_event_next_query new_event_in_next_born generated_source_return actual_full_source_return)
end R
namespace B
export SourceGeneratedInquiryReceiptAction.Inventory.Born
 (inventory bornFrame lowInventory original_low_inventory original_expression original_relation
  born_occurrence lowRaw physicalRaw physicalInventory migratedEvent)
end B
variable {Sorts : Type u} {Value Var : Sorts → Type u}
 [∀ target, AddCommGroup (Value target)] {sort : Sorts}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value := Value) (Var := Var) (sort := sort))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))

theorem source_event_exists : (R.eventReceipt frame configuration).1 ∈ (R.written frame configuration).trace :=
 (R.eventReceipt frame configuration).2.down

theorem born_field_is_real : (B.bornFrame frame configuration).inventory = some (B.inventory frame configuration) := rfl

theorem root_reaches_next_query : type_of%
 (R.new_event_next_query frame configuration (R.eventReceipt frame configuration).1
  (source_event_exists frame configuration)) :=
 R.new_event_next_query frame configuration (R.eventReceipt frame configuration).1 (source_event_exists frame configuration)

theorem root_in_next_born_inventory : type_of%
 (R.new_event_in_next_born frame configuration (R.eventReceipt frame configuration).1
  (source_event_exists frame configuration)) :=
 R.new_event_in_next_born frame configuration (R.eventReceipt frame configuration).1 (source_event_exists frame configuration)

theorem all_fresh_events_written (event) (present : event ∈ (R.written frame configuration).trace) :
 event ∈ (B.inventory frame configuration).trace :=
 R.new_event_born frame configuration event present

theorem source_binding_expression (expression : Expr (PairValue Value) Var sort) : type_of%
 (B.original_expression frame configuration expression) :=
 B.original_expression frame configuration expression

theorem source_binding_relation (word : Formal ℤ (PairValue Value) Var sort) : type_of%
 (B.original_relation frame configuration word) :=
 B.original_relation frame configuration word

theorem actual_born_occurrence : type_of% (B.born_occurrence frame configuration) :=
 B.born_occurrence frame configuration

theorem generated_whole_inverse_next : type_of% (R.generated_source_return frame configuration) :=
 R.generated_source_return frame configuration

variable (initial : SourceOperationInquiry.Context.Native.Frame.SourceFrame (Value := Value) (Var := Var) (sort := sort))
theorem actual_full_frame_return (stage : Nat) : type_of% (R.actual_full_source_return configuration initial stage) :=
 R.actual_full_source_return configuration initial stage

-- Different source languages require the existing binding, rather than a direct event cast.
#check_failure fun (event : PresentedRelationEventAt (Expr (PairValue Value) Var sort)) =>
 (show PresentedRelationEventAt (Expr (PairValue Value) configuration.LowVar sort) from event)

#print axioms source_event_exists
#print axioms born_field_is_real
#print axioms root_reaches_next_query
#print axioms root_in_next_born_inventory
#print axioms all_fresh_events_written
#print axioms source_binding_expression
#print axioms source_binding_relation
#print axioms actual_born_occurrence
#print axioms generated_whole_inverse_next
#print axioms actual_full_frame_return
end SourcePolicyQueryTraceReturnControls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
