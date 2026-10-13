import H0mework.Versions.Raef0ad2a.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.InventoryTransport
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
abbrev born := Shared.nextBorn frame (continuedConfiguration seed)
abbrev currentHistory := InventoryTransport.currentHistory seed frame
abbrev bornHistory := InventoryTransport.bornHistory seed (born seed frame)
theorem written_preserves : ∀ event ∈ (written seed frame).trace,
    event ∈ (pairInventory seed (epoch (born seed frame)) (Shared.actualOccurrence (born seed frame))).trace := by
  intro event belongs
  apply (SourceHistoryCommon.parallel_left _ _ _).1
  unfold priorPairInventory
  change event ∈ (SourceHistoryCommon.seed (written seed frame)
    (liftedInventory seed (epoch (born seed frame)) (Shared.actualOccurrence (born seed frame)))).trace
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event belongs
abbrev born_pair_preserves := InventoryTransport.born_pair_preserves seed frame (born seed frame) (written_preserves seed frame)
abbrev completionTransition := InventoryTransport.completionTransition seed frame (born seed frame) (written_preserves seed frame)
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
variable (sound : GeneratedRelationSoundnessAt (Joint.face seed (epoch frame) (Shared.actualOccurrence frame)))
variable (obstruction : GeneratedCoverageResidualObstructionAt (Joint.face seed (epoch frame) (Shared.actualOccurrence frame)) sound)
variable (coordinate : GeneratedKernelResidualCoordinateAt (Joint.face seed (epoch frame) (Shared.actualOccurrence frame)) sound)
variable (selected : Joint.disposition seed (epoch frame) (Shared.actualOccurrence frame) = .kernelResidual sound obstruction coordinate)
abbrev born_kernel_member := InventoryTransport.born_kernel_member seed frame (born seed frame) (written_preserves seed frame) sound obstruction coordinate selected
abbrev born_kernel_zero := InventoryTransport.born_kernel_zero seed frame (born seed frame) (written_preserves seed frame) sound obstruction coordinate selected
abbrev OutputAt := InventoryTransport.OutputAt seed frame (born seed frame) (written_preserves seed frame)
abbrev output := InventoryTransport.output seed frame (born seed frame) (written_preserves seed frame)
end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
