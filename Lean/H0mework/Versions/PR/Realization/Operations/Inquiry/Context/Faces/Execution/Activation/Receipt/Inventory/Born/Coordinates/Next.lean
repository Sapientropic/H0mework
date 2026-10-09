import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Coordinates.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CofinalHistorySettlement CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair (face disposition relationWrite kernelWord)
end Q
abbrev currentFrame := A.epoch (bornFrame frame configuration)
abbrev currentOccurrence := Shared.actualOccurrence (bornFrame frame configuration)
abbrev selected := Q.disposition (seed frame configuration) (currentFrame frame configuration) (currentOccurrence frame configuration)
abbrev written := Q.relationWrite (seed frame configuration) (currentFrame frame configuration)
 (currentOccurrence frame configuration) (selected frame configuration)
def intoWrittenAt (outcome : ResidualDispositionOutcome (Q.face (seed frame configuration)
 (currentFrame frame configuration) (currentOccurrence frame configuration)))
 (index : Fin (combined frame configuration).trace.length) :
 Fin (Q.relationWrite (seed frame configuration) (currentFrame frame configuration)
  (currentOccurrence frame configuration) outcome).trace.length :=
 match outcome with
 | .kernelResidual sound _ coordinate => SourceHistoryCommon.Coordinates.left (combined frame configuration)
    (.zero (.relation (Q.kernelWord (seed frame configuration) (currentFrame frame configuration)
      (currentOccurrence frame configuration) sound coordinate).val)) index
 | .faithful _ _ _ | .unsound _ _ | .coverageResidual _ _ _ => index
abbrev intoWritten := intoWrittenAt frame configuration (selected frame configuration)
theorem written_injective : Function.Injective (intoWritten frame configuration) := by
 unfold intoWritten
 cases selected frame configuration with
 | kernelResidual _ _ _ => exact SourceHistoryCommon.Coordinates.left_injective _ _
 | faithful _ _ _ | unsound _ _ | coverageResidual _ _ _ => exact Function.injective_id
theorem written_read (index : Fin (combined frame configuration).trace.length) :
 (written frame configuration).trace.get (intoWritten frame configuration index)=(combined frame configuration).trace.get index := by
 unfold intoWritten written Q.relationWrite
 cases selected frame configuration with
 | kernelResidual _ _ _ => exact SourceHistoryCommon.Coordinates.left_read _ _ _
 | faithful _ _ _ | unsound _ _ | coverageResidual _ _ _ => rfl
abbrev nextFrame := Shared.nextBorn (bornFrame frame configuration) (consumer frame configuration)
abbrev nextPaid := SourceOperationPaidRelations.exposure (P.physical (A.epoch (nextFrame frame configuration))
 (Shared.actualOccurrence (nextFrame frame configuration))).paid.state.2
abbrev nextPrior := SourceHistoryCommon.seed (seed frame configuration) (written frame configuration)
abbrev nextInventory := P.updatedSeed (seed frame configuration) (A.epoch (nextFrame frame configuration))
 (Shared.actualOccurrence (nextFrame frame configuration))
def intoNext (index : Vector.Index frame configuration) : Fin (nextInventory frame configuration).trace.length :=
 SourceHistoryCommon.Coordinates.left (nextPrior frame configuration) (nextPaid frame configuration)
  (SourceHistoryCommon.Coordinates.right (seed frame configuration) (written frame configuration)
   (intoWritten frame configuration (intoCofinal frame configuration index)))
theorem next_injective : Function.Injective (intoNext frame configuration) :=
 (SourceHistoryCommon.Coordinates.left_injective _ _).comp
  ((SourceHistoryCommon.Coordinates.right_injective _ _).comp ((written_injective frame configuration).comp (injective frame configuration)))
theorem next_event_read (index : Vector.Index frame configuration) :
 (nextInventory frame configuration).trace.get (intoNext frame configuration index)=Vector.event frame configuration index :=
 (SourceHistoryCommon.Coordinates.left_read _ _ _).trans
  ((SourceHistoryCommon.Coordinates.right_read _ _ _).trans
   ((written_read frame configuration _).trans (event_read frame configuration index)))
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
