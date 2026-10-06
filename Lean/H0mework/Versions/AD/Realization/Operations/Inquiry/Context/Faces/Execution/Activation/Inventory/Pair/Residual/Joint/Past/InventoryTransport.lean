import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.InventoryTransport
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
variable (target : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
variable (preserved : ∀ event ∈ (Past.written seed frame).trace,
  event ∈ (pairInventory seed (epoch target) (Shared.actualOccurrence target)).trace)
abbrev currentHistory := Joint.history seed (epoch frame) (Shared.actualOccurrence frame)
abbrev bornHistory := Joint.history seed (epoch target) (Shared.actualOccurrence target)
include preserved in
theorem born_pair_preserves :
    ∀ event ∈ (pairInventory seed (epoch frame) (Shared.actualOccurrence frame)).trace,
      event ∈ (pairInventory seed (epoch target) (Shared.actualOccurrence target)).trace := by
  intro event belongs
  exact preserved event (Past.current_written_preserved seed frame event
    (Joint.complete_written_preserves seed (epoch frame) _ event belongs))

def completionTransition : CofinalHistoryTransition.GeneratedTransition
    (currentHistory seed frame) (bornHistory seed target) :=
  CofinalHistoryTransition.GeneratedTransition.create _ _
    (SourceOperationPaidRelations.generators_next _ _ _ _ (born_pair_preserves seed frame target preserved)) (by
      intro direction belongs
      change (bornHistory seed target).completionProjection
        ⟨direction.val,SourceOperationPaidRelations.generators_next _ _ _ _
          (born_pair_preserves seed frame target preserved) direction.property⟩ = 0
      apply (Submodule.Quotient.mk_eq_zero _).2
      exact SourceOperationPaidRelations.relations_next _ _ _ _ (born_pair_preserves seed frame target preserved) belongs)

open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
variable (sound : GeneratedRelationSoundnessAt (Joint.face seed (epoch frame) (Shared.actualOccurrence frame)))
variable (obstruction : GeneratedCoverageResidualObstructionAt
  (Joint.face seed (epoch frame) (Shared.actualOccurrence frame)) sound)
variable (coordinate : GeneratedKernelResidualCoordinateAt
  (Joint.face seed (epoch frame) (Shared.actualOccurrence frame)) sound)
variable (selected : Joint.disposition seed (epoch frame) (Shared.actualOccurrence frame) =
  .kernelResidual sound obstruction coordinate)
include obstruction selected preserved in
theorem born_kernel_member :
    (Joint.kernelWord seed (epoch frame) (Shared.actualOccurrence frame) sound coordinate).val ∈
      (bornHistory seed target).relationClosure := by
  apply (bornHistory seed target).relationStage_le_closure 0
  apply Submodule.subset_span
  change PresentedRelationEventAt.relation _ ∈ (bornHistory seed target).observedEvents 0
  simp only [RootGeneratedCofinalHistoryAt.observedEvents,List.range_succ,List.range_zero,
    List.nil_append,List.flatMap_singleton,RootGeneratedCofinalHistoryAt.observation_zero]
  apply preserved
  apply Past.current_written_preserved seed frame
  apply (SourceHistoryCommon.parallel_left _ _ _).1
  rw [selected]
  exact (SourceHistoryCommon.parallel_right _ _ _).1 _
    (RootedAccountedUnfolding.zero (PresentedRelationEventAt.relation
      (Joint.kernelWord seed (epoch frame) (Shared.actualOccurrence frame) sound coordinate).val)).root_mem_trace

include obstruction selected in
theorem born_kernel_zero : CofinalHistoryTransition.GeneratedTransition.completionMap _ _
    (completionTransition seed frame target preserved) coordinate.coordinate.val = 0 := by
  rw [← Joint.kernel_word_read seed (epoch frame) (Shared.actualOccurrence frame) sound coordinate]
  apply (SourceHistoryCommon.transition_fibre_zero _ _ _ _).mpr
  exact born_kernel_member seed frame target preserved sound obstruction coordinate selected

def OutputAt (phase : ResidualDispositionOutcome
    (Joint.face seed (epoch frame) (Shared.actualOccurrence frame))) : Type u :=
  match phase with
  | .faithful _ _ _ => (currentHistory seed frame).CompletionCarrier ≃+ PairValue PhysicalValue sort
  | .kernelResidual _ _ selectedCoordinate => ULift.{u,0} (PLift (CofinalHistoryTransition.GeneratedTransition.completionMap _ _
      (completionTransition seed frame target preserved) selectedCoordinate.coordinate.val = 0))
  | .unsound _ selectedCoordinate => type_of% selectedCoordinate
  | .coverageResidual _ _ selectedCoordinate => type_of% selectedCoordinate

def output : OutputAt seed frame target preserved (Joint.disposition seed (epoch frame) (Shared.actualOccurrence frame)) := by
  generalize selectedEq : Joint.disposition seed (epoch frame) (Shared.actualOccurrence frame) = phase
  cases phase with
  | faithful selectedSound coverage realization => exact realization.canonicalQuotientAddEquiv
  | kernelResidual selectedSound selectedObstruction selectedCoordinate =>
      exact ⟨⟨born_kernel_zero seed frame target preserved selectedSound selectedObstruction selectedCoordinate selectedEq⟩⟩
  | unsound _ selectedCoordinate => exact selectedCoordinate
  | coverageResidual _ _ selectedCoordinate => exact selectedCoordinate

end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.InventoryTransport
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
