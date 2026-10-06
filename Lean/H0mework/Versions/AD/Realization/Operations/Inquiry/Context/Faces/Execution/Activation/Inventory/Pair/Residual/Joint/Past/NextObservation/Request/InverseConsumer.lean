import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.Installation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Inverse
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
abbrev sourceResult := (sourceFace seed frame).rootRead.2.2.2.2
theorem source_result : HEq (sourceResult seed frame)
    (result seed (epoch frame) (Shared.actualOccurrence frame)) := HEq.rfl

theorem raw_next : type_of% (next_raw_actual seed frame (installedConfiguration seed) rfl) :=
  next_raw_actual seed frame (installedConfiguration seed) rfl
theorem value_read : (sourceResult seed frame).2.2.1 =
    (occurrenceRaw seed (epoch frame) (Shared.actualOccurrence frame)).expression.eval
      (nextEnvironment (epoch frame) (Shared.actualOccurrence frame)) :=
  generated_value seed (epoch frame) (Shared.actualOccurrence frame)
theorem fee_read : (sourceResult seed frame).2.1.2.length =
    remaining (occurrenceRaw seed (epoch frame) (Shared.actualOccurrence frame)).expression :=
  generated_cost seed (epoch frame) (Shared.actualOccurrence frame)
theorem full_trace_written (event : PresentedRelationEventAt (Expr (PairValue PhysicalValue) PhysicalVar sort))
    (present : event ∈ (SourceOperationPaidRelations.exposure (sourceResult seed frame).2.1.2).trace) :
    event ∈ (installedWritten seed frame).trace :=
  inverse_trace_written seed frame event present
end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Inverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
