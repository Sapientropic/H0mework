import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Vector.Action.Consumer
import H0mework.Realization.Perfectification.Occurrence.Temporal.History.Common.Coordinates
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
abbrev prior := SourceHistoryCommon.seed (seed frame configuration) (inventory frame configuration)
abbrev paid := SourceOperationPaidRelations.exposure (P.physical (A.epoch (bornFrame frame configuration))
 (Shared.actualOccurrence (bornFrame frame configuration))).paid.state.2
abbrev combined := P.updatedSeed (seed frame configuration) (A.epoch (bornFrame frame configuration))
 (Shared.actualOccurrence (bornFrame frame configuration))
def intoCofinal (index : Vector.Index frame configuration) : Fin (combined frame configuration).trace.length :=
 SourceHistoryCommon.Coordinates.left (prior frame configuration) (paid frame configuration)
  (SourceHistoryCommon.Coordinates.right (seed frame configuration) (inventory frame configuration) index)
theorem injective : Function.Injective (intoCofinal frame configuration) :=
 (SourceHistoryCommon.Coordinates.left_injective _ _).comp (SourceHistoryCommon.Coordinates.right_injective _ _)
theorem event_read (index : Vector.Index frame configuration) :
 (combined frame configuration).trace.get (intoCofinal frame configuration index)=Vector.event frame configuration index :=
 (SourceHistoryCommon.Coordinates.left_read _ _ _).trans (SourceHistoryCommon.Coordinates.right_read _ _ _)
def inventoryEventWord : PresentedRelationEventAt (Expr (PairValue PhysicalValue) configuration.LowVar slot) →
 SourceOperationScalarRelations.Formal ℤ (PairValue PhysicalValue) configuration.LowVar slot
 | .generator expression => Finsupp.single expression 1
 | .relation relation => relation
def cofinalWord (index : Fin (combined frame configuration).trace.length) :=
 inventoryEventWord configuration ((combined frame configuration).trace.get index)
theorem word_read (index : Vector.Index frame configuration) : cofinalWord frame configuration
 (intoCofinal frame configuration index)=Vector.word frame configuration index :=
 congrArg (inventoryEventWord configuration) (event_read frame configuration index)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
