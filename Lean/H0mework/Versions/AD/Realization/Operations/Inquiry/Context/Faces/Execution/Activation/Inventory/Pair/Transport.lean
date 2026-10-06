import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Consumer
import H0mework.Realization.Operations.Execution.Relations.History.Append
import H0mework.Realization.Operations.Execution.Relations.History.Monotone
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations CofinalHistorySettlement
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
theorem inventory_next : ∀ atom ∈ (updatedSeed seed (epoch frame) (Shared.actualOccurrence frame)).trace,
    atom ∈ (updatedSeed seed (epoch (Shared.next frame (programme seed)))
      (Shared.actualOccurrence (Shared.next frame (programme seed)))).trace := by
  unfold Shared.next
  cases frame.action with
  | inl settled => exact birth_inventory_preserved seed frame
  | inr paid => exact InventoryProgramme.inventory_math_next seed frame

def transition : CofinalHistoryTransition.GeneratedTransition
    (InventoryProgramme.history seed (epoch frame) (Shared.actualOccurrence frame))
    (InventoryProgramme.history seed (epoch (Shared.next frame (programme seed)))
      (Shared.actualOccurrence (Shared.next frame (programme seed)))) :=
  CofinalHistoryTransition.GeneratedTransition.create _ _
    (SourceOperationPaidRelations.generators_next _ _ _ _ (inventory_next seed frame)) (by
      intro word belongs
      change (InventoryProgramme.history seed (epoch (Shared.next frame (programme seed)))
        (Shared.actualOccurrence (Shared.next frame (programme seed)))).completionProjection
          ⟨word.val,SourceOperationPaidRelations.generators_next _ _ _ _ (inventory_next seed frame) word.property⟩ = 0
      apply (Submodule.Quotient.mk_eq_zero _).2
      exact SourceOperationPaidRelations.relations_next _ _ _ _ (inventory_next seed frame) belongs)


open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
variable (sound : GeneratedRelationSoundnessAt (face seed (epoch frame) (Shared.actualOccurrence frame)))
variable (obstruction : GeneratedCoverageResidualObstructionAt (face seed (epoch frame) (Shared.actualOccurrence frame)) sound)
variable (coordinate : GeneratedKernelResidualCoordinateAt (face seed (epoch frame) (Shared.actualOccurrence frame)) sound)
variable (selected : disposition seed (epoch frame) (Shared.actualOccurrence frame) = .kernelResidual sound obstruction coordinate)
include obstruction selected in
theorem birth_kernel_relation : (kernelWord seed (epoch frame) (Shared.actualOccurrence frame) sound coordinate).val ∈
    (InventoryProgramme.history seed (epoch (Shared.nextBorn frame (programme seed)))
      (Shared.actualOccurrence (Shared.nextBorn frame (programme seed)))).relationClosure := by
  apply (InventoryProgramme.history seed (epoch (Shared.nextBorn frame (programme seed)))
    (Shared.actualOccurrence (Shared.nextBorn frame (programme seed)))).relationStage_le_closure 0
  apply Submodule.subset_span
  change PresentedRelationEventAt.relation (kernelWord seed (epoch frame) (Shared.actualOccurrence frame) sound coordinate).val ∈
    (InventoryProgramme.history seed (epoch (Shared.nextBorn frame (programme seed)))
      (Shared.actualOccurrence (Shared.nextBorn frame (programme seed)))).observedEvents 0
  simp only [RootGeneratedCofinalHistoryAt.observedEvents,List.range_succ,List.range_zero,List.nil_append,
    List.flatMap_singleton,RootGeneratedCofinalHistoryAt.observation_zero]
  apply (SourceHistoryCommon.parallel_left _ _ _).1
  apply (SourceHistoryCommon.parallel_right _ _ _).1
  change PresentedRelationEventAt.relation (kernelWord seed (epoch frame) (Shared.actualOccurrence frame) sound coordinate).val ∈
    (relationWrite seed (epoch frame) (Shared.actualOccurrence frame)
      (disposition seed (epoch frame) (Shared.actualOccurrence frame))).trace
  rw [selected]
  exact (SourceHistoryCommon.parallel_right _ _ _).1 _
    (RootedAccountedUnfolding.zero (PresentedRelationEventAt.relation
      (kernelWord seed (epoch frame) (Shared.actualOccurrence frame) sound coordinate).val)).root_mem_trace

variable (settled : SourceOperationExecutionDebt.Settlement frame.event.state) (action : frame.action = .inl settled)
include obstruction selected settled action in
theorem actual_kernel_paid : CofinalHistoryTransition.GeneratedTransition.completionMap
    (InventoryProgramme.history seed (epoch frame) (Shared.actualOccurrence frame))
    (InventoryProgramme.history seed (epoch (Shared.next frame (programme seed)))
      (Shared.actualOccurrence (Shared.next frame (programme seed))))
    (transition seed frame) coordinate.coordinate.val = 0 := by
  rw [← kernel_word_read seed (epoch frame) (Shared.actualOccurrence frame) sound coordinate]
  apply (SourceHistoryCommon.transition_fibre_zero _ _ _ _).mpr
  unfold Shared.next
  rw [action]
  exact birth_kernel_relation seed frame sound obstruction coordinate selected

end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
