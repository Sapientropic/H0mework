import H0mework.Versions.R9c73a630.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Consumer
import H0mework.Versions.R9c73a630.Realization.Operations.Inquiry.Context.Native.Frame.Stock
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Frame.Stock.Return
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CofinalHistorySettlement
namespace I
export SourceGeneratedInquiryReceiptAction.Inventory
 (programme actual_trace_written completeWritten)
end I
namespace B
export SourceGeneratedInquiryReceiptAction.Inventory.Born
 (lowInventory original_low_inventory low_event inventory cofinal_input born_occurrence
  actual_query next_inventory whole_first literal_next actual_update actual_inverse no_refill noetherian)
end B
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (resultFace query actualOccurrence)
end A
variable {Sorts : Type u} {Value Var : Sorts → Type u}
 [∀ target, AddCommGroup (Value target)] {sort : Sorts}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value := Value) (Var := Var) (sort := sort))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))

abbrev queryTrace := (A.resultFace frame (I.programme configuration)).rootRead.2.1.2
abbrev written := SourceOperationPaidRelations.exposure (queryTrace frame configuration)

theorem new_event_born (event) (present : event ∈ (written frame configuration).trace) :
 event ∈ (B.inventory frame configuration).trace := by
 have generated := I.actual_trace_written frame configuration event present
 apply B.low_event frame configuration event
 rw [B.original_low_inventory]
 exact generated

theorem new_event_next_query (event) (present : event ∈ (written frame configuration).trace) :
 type_of% (B.cofinal_input frame configuration event (new_event_born frame configuration event present)) :=
 B.cofinal_input frame configuration event (new_event_born frame configuration event present)

theorem new_event_in_next_born (event) (present : event ∈ (written frame configuration).trace) :
 type_of% (B.next_inventory frame configuration event (new_event_born frame configuration event present)) :=
 B.next_inventory frame configuration event (new_event_born frame configuration event present)

theorem actual_source_return (event) (present : event ∈ (written frame configuration).trace) :
 (event ∈ (B.inventory frame configuration).trace) ∧
 type_of% (B.actual_query frame configuration) ∧
 type_of% (B.whole_first frame configuration) ∧
 type_of% (B.literal_next frame configuration) ∧
 type_of% (B.actual_update frame configuration) ∧
 type_of% (B.actual_inverse frame configuration) ∧
 type_of% (B.no_refill frame configuration) ∧
 type_of% (B.noetherian frame configuration) :=
 ⟨new_event_born frame configuration event present, B.actual_query frame configuration,
  B.whole_first frame configuration, B.literal_next frame configuration,
  B.actual_update frame configuration, B.actual_inverse frame configuration,
  B.no_refill frame configuration, B.noetherian frame configuration⟩

def eventReceipt : Σ event, PLift (event ∈ (written frame configuration).trace) :=
 ⟨(written frame configuration).root, ⟨RootedAccountedUnfolding.root_mem_trace _⟩⟩

theorem generated_source_return : type_of%
 (actual_source_return frame configuration (eventReceipt frame configuration).1
  (eventReceipt frame configuration).2.down) :=
 actual_source_return frame configuration (eventReceipt frame configuration).1
  (eventReceipt frame configuration).2.down

variable (initial : SourceFrame (Value := Value) (Var := Var) (sort := sort))

theorem actual_full_source_return (stage : Nat) : type_of%
 (generated_source_return (Stock.frameAt initial configuration (stage + 1)) configuration) :=
 generated_source_return (Stock.frameAt initial configuration (stage + 1)) configuration

end SourceOperationInquiry.Context.Native.Frame.Stock.Return
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
