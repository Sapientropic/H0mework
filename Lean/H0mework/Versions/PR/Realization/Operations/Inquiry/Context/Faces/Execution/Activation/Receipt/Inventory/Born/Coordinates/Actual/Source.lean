import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Coordinates.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
def inventoryAt (sourceFrame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PairValue PhysicalValue) (Var:=configuration.LowVar) (sort:=slot)) :=
 P.updatedSeed (seed frame configuration) (A.epoch sourceFrame) (Shared.actualOccurrence sourceFrame)
def nextFrom (sourceFrame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PairValue PhysicalValue) (Var:=configuration.LowVar) (sort:=slot))
 (choice : sourceFrame.Action) := match choice with
 | .inr _ => sourceFrame.mathNext
 | .inl _ => SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn sourceFrame (consumer frame configuration)
def inventoryFrom (sourceFrame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PairValue PhysicalValue) (Var:=configuration.LowVar) (sort:=slot))
 (choice : sourceFrame.Action) := inventoryAt frame configuration (nextFrom frame configuration sourceFrame choice)
abbrev actualFrame := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next (bornFrame frame configuration)
 (consumer frame configuration)
def actualInventory := inventoryFrom frame configuration (bornFrame frame configuration) (bornFrame frame configuration).action
def mathIndex : Vector.Index frame configuration →
 Fin (inventoryAt frame configuration (bornFrame frame configuration).mathNext).trace.length :=
 fun index => SourceHistoryCommon.Coordinates.left (prior frame configuration)
  (SourceOperationPaidRelations.exposure (P.physical (A.epoch (bornFrame frame configuration))
    (Shared.actualOccurrence (bornFrame frame configuration).mathNext)).paid.state.2)
  (SourceHistoryCommon.Coordinates.right (seed frame configuration) (inventory frame configuration) index)
def intoAt (choice : (bornFrame frame configuration).Action) : Vector.Index frame configuration →
 Fin (inventoryFrom frame configuration (bornFrame frame configuration) choice).trace.length :=
 match choice with
 | .inl _ => intoNext frame configuration
 | .inr _ => mathIndex frame configuration
abbrev intoActual := intoAt frame configuration (bornFrame frame configuration).action
theorem math_read (index : Vector.Index frame configuration) :
 (inventoryAt frame configuration (bornFrame frame configuration).mathNext).trace.get (mathIndex frame configuration index)=
 Vector.event frame configuration index :=
 (SourceHistoryCommon.Coordinates.left_read _ _ _).trans (SourceHistoryCommon.Coordinates.right_read _ _ _)
theorem intoAt_injective (choice : (bornFrame frame configuration).Action) : Function.Injective (intoAt frame configuration choice) := by
 cases choice with
 | inl settled => exact next_injective frame configuration
 | inr paid => exact (SourceHistoryCommon.Coordinates.left_injective _ _).comp (SourceHistoryCommon.Coordinates.right_injective _ _)
theorem intoAt_event_read (choice : (bornFrame frame configuration).Action) (index : Vector.Index frame configuration) :
 (inventoryFrom frame configuration (bornFrame frame configuration) choice).trace.get (intoAt frame configuration choice index)=
 Vector.event frame configuration index := by
 cases choice with
 | inl settled => exact next_event_read frame configuration index
 | inr paid => exact math_read frame configuration index
theorem actual_injective : Function.Injective (intoActual frame configuration) :=
 intoAt_injective frame configuration (bornFrame frame configuration).action
theorem actual_event_read (index : Vector.Index frame configuration) :
 (actualInventory frame configuration).trace.get (intoActual frame configuration index)=Vector.event frame configuration index :=
 intoAt_event_read frame configuration (bornFrame frame configuration).action index
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
