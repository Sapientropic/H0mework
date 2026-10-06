import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Written
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
attribute [local instance] Reverse.valueGroup
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
variable (sourceStage stage : Nat)
namespace R
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual (liftEvent)
end R
namespace C
export Inventory.Born (stock inventory bornFrame consumer generated)
end C
abbrev sourceExposure := SourceOperationPaidRelations.exposure (Action.trace frame configuration sourceStage stage)
abbrev queryExposure := SourceOperationPaidRelations.exposure (Action.result frame configuration sourceStage stage).2.1.2
def prior := SourceHistoryCommon.seed ((sourceExposure frame configuration sourceStage stage).map R.liftEvent)
 (queryExposure frame configuration sourceStage stage)
def sourceFrame := {Action.queryFrame frame configuration sourceStage stage with
 inventory:=some (prior frame configuration sourceStage stage)}
abbrev stock := C.stock (sourceFrame frame configuration sourceStage stage)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme
abbrev inventory := C.inventory (sourceFrame frame configuration sourceStage stage)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme
abbrev bornFrame := C.bornFrame (sourceFrame frame configuration sourceStage stage)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme
abbrev consumer := C.consumer (sourceFrame frame configuration sourceStage stage)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme
abbrev generated := (Action.generated frame configuration sourceStage stage,prior frame configuration sourceStage stage,
 stock frame configuration sourceStage stage,C.generated (sourceFrame frame configuration sourceStage stage)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Written
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
