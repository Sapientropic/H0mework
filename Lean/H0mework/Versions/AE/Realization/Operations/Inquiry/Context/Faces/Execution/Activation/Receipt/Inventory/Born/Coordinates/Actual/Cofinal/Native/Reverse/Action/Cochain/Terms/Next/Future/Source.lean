import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future
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
namespace J
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint
 (runtime physicalSource physicalField frameAt generated configuration queryAt answerAt nextAt full_scalar_inventory no_refill noetherian)
end J
abbrev sourceFrame := Next.queryFrame frame configuration sourceStage stage
abbrev initial := Inventory.Born.bornFrame (sourceFrame frame configuration sourceStage stage)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme
abbrev seed := Inventory.Born.seed (sourceFrame frame configuration sourceStage stage)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme
abbrev consumer := Inventory.Born.consumer (sourceFrame frame configuration sourceStage stage)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme
abbrev runtime := J.runtime (seed frame configuration sourceStage stage) (initial frame configuration sourceStage stage)
abbrev source := J.physicalSource (seed frame configuration sourceStage stage) (initial frame configuration sourceStage stage)
abbrev frameAt (count : Nat) := J.frameAt (seed frame configuration sourceStage stage) (initial frame configuration sourceStage stage) count
abbrev field (count : Nat) := J.physicalField (seed frame configuration sourceStage stage) (initial frame configuration sourceStage stage) count
namespace C
export SourceOperationInquiry.Context.Faces.Cofinal (relationAt relationField relationWitness)
end C
abbrev word (count : Nat) := C.relationAt (runtime frame configuration sourceStage stage)
 (source frame configuration sourceStage stage) count
abbrev relationField (count : Nat) := C.relationField (runtime frame configuration sourceStage stage)
 (source frame configuration sourceStage stage) count
abbrev witness (count : Nat) := C.relationWitness (runtime frame configuration sourceStage stage)
 (source frame configuration sourceStage stage) count
abbrev originalGenerated := J.generated (seed frame configuration sourceStage stage) (initial frame configuration sourceStage stage)
abbrev queryGenerated (count queryCount : Nat) := Actual.Cofinal.generated
 (frameAt frame configuration sourceStage stage count) (consumer frame configuration sourceStage stage) queryCount
abbrev generated := (Next.generated frame configuration sourceStage stage,originalGenerated frame configuration sourceStage stage,
 word frame configuration sourceStage stage,relationField frame configuration sourceStage stage,witness frame configuration sourceStage stage,
 queryGenerated frame configuration sourceStage stage)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Cochain.Terms.Next.Future
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
