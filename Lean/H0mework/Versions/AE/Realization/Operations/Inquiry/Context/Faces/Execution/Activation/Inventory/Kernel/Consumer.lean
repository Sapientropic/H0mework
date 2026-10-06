import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Kernel.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.KernelWrite
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations CofinalHistorySettlement SourceOperationScalarPresentation
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
variable (sound : GeneratedRelationSoundnessAt (face seed (epoch frame) (Shared.actualOccurrence frame)))
variable (obstruction : GeneratedCoverageResidualObstructionAt (face seed (epoch frame) (Shared.actualOccurrence frame)) sound)
variable (coordinate : GeneratedKernelResidualCoordinateAt (face seed (epoch frame) (Shared.actualOccurrence frame)) sound)
variable (selected : disposition seed (epoch frame) (Shared.actualOccurrence frame) = .kernelResidual sound obstruction coordinate)
abbrev bornHistory := history seed (epoch (Shared.nextBorn frame (programme seed)))
  (Shared.actualOccurrence (Shared.nextBorn frame (programme seed)))

include obstruction selected in
theorem birth_word_member : word seed (epoch frame) (Shared.actualOccurrence frame) sound coordinate ∈
    (bornHistory seed frame).relationClosure := by
  apply (bornHistory seed frame).relationStage_le_closure 0
  apply Submodule.subset_span
  change PresentedRelationEventAt.relation (word seed (epoch frame) (Shared.actualOccurrence frame) sound coordinate) ∈
    (bornHistory seed frame).observedEvents 0
  simp only [RootGeneratedCofinalHistoryAt.observedEvents,List.range_succ,List.range_zero,
    List.nil_append,List.flatMap_singleton,RootGeneratedCofinalHistoryAt.observation_zero]
  apply (SourceHistoryCommon.parallel_left _ _ _).1
  change PresentedRelationEventAt.relation (word seed (epoch frame) (Shared.actualOccurrence frame) sound coordinate) ∈
    (SourceHistoryCommon.seed seed (writtenSeed seed (epoch frame) (Shared.actualOccurrence frame))).trace
  apply (SourceHistoryCommon.parallel_right _ _ _).1
  unfold writtenSeed
  rw [selected]
  exact (SourceHistoryCommon.parallel_right _ _ _).1 _
    (relationEvent seed (epoch frame) (Shared.actualOccurrence frame) sound coordinate).root_mem_trace

def birthTransition : CofinalHistoryTransition.GeneratedTransition
    (history seed (epoch frame) (Shared.actualOccurrence frame)) (bornHistory seed frame) :=
  CofinalHistoryTransition.GeneratedTransition.create _ _
    (SourceOperationPaidRelations.generators_next _ _ _ _ (birth_inventory_preserved seed frame)) (by
      intro direction belongs
      change (bornHistory seed frame).completionProjection
        ⟨direction.val,SourceOperationPaidRelations.generators_next _ _ _ _
          (birth_inventory_preserved seed frame) direction.property⟩ = 0
      apply (Submodule.Quotient.mk_eq_zero _).2
      exact SourceOperationPaidRelations.relations_next _ _ _ _ (birth_inventory_preserved seed frame) belongs)

include obstruction selected in
theorem birth_coordinate_paid : CofinalHistoryTransition.GeneratedTransition.completionMap
    (history seed (epoch frame) (Shared.actualOccurrence frame)) (bornHistory seed frame)
    (birthTransition seed frame) coordinate.coordinate.val = 0 := by
  rw [← kernel_word_read seed (epoch frame) (Shared.actualOccurrence frame) sound coordinate]
  apply (SourceHistoryCommon.transition_fibre_zero _ _ _ _).mpr
  exact birth_word_member seed frame sound obstruction coordinate selected

-- Actual settlement selects the same original admission target, not a sibling next.
variable (settled : SourceOperationExecutionDebt.Settlement frame.event.state)
variable (action : frame.action = .inl settled)
include obstruction selected settled action in
theorem actual_coordinate_paid : CofinalHistoryTransition.GeneratedTransition.completionMap
    (history seed (epoch frame) (Shared.actualOccurrence frame))
    (history seed (epoch (Shared.next frame (programme seed)))
      (Shared.actualOccurrence (Shared.next frame (programme seed))))
    (InventoryProgramme.transition seed frame) coordinate.coordinate.val = 0 := by
  rw [← kernel_word_read seed (epoch frame) (Shared.actualOccurrence frame) sound coordinate]
  apply (SourceHistoryCommon.transition_fibre_zero _ _ _ _).mpr
  unfold Shared.next
  rw [action]
  exact birth_word_member seed frame sound obstruction coordinate selected
end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.KernelWrite
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
