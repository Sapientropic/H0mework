import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Consumer
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.RawState
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarInventoryLift CofinalHistorySettlement
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : Context.Installation.Occurrence frame (current:=current))
theorem born_inventory_preserves :
    ∀ event ∈ (pairInventory seed (epoch frame) (Shared.actualOccurrence frame)).trace,
      event ∈ (pairInventory seed (epoch (Shared.nextBorn frame (configuration seed)))
        (Shared.actualOccurrence (Shared.nextBorn frame (configuration seed)))).trace := by
  intro event belongs
  apply (SourceHistoryCommon.parallel_left _ _ _).1
  unfold priorPairInventory
  change event ∈ (SourceHistoryCommon.seed
    (completeWrittenInventory seed (epoch frame) (Shared.actualOccurrence frame))
    (liftedInventory seed (epoch (Shared.nextBorn frame (configuration seed)))
      (Shared.actualOccurrence (Shared.nextBorn frame (configuration seed))))).trace
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event (complete_written_preserves seed (epoch frame) _ event belongs)

def birthTransition : CofinalHistoryTransition.GeneratedTransition
    (history seed (epoch frame) (Shared.actualOccurrence frame))
    (history seed (epoch (Shared.nextBorn frame (configuration seed)))
      (Shared.actualOccurrence (Shared.nextBorn frame (configuration seed)))) :=
  CofinalHistoryTransition.GeneratedTransition.create _ _
    (SourceOperationPaidRelations.generators_next _ _ _ _ (born_inventory_preserves seed frame)) (by
      intro direction belongs
      change (history seed (epoch (Shared.nextBorn frame (configuration seed)))
        (Shared.actualOccurrence (Shared.nextBorn frame (configuration seed)))).completionProjection
          ⟨direction.val,SourceOperationPaidRelations.generators_next _ _ _ _
            (born_inventory_preserves seed frame) direction.property⟩ = 0
      apply (Submodule.Quotient.mk_eq_zero _).2
      exact SourceOperationPaidRelations.relations_next _ _ _ _ (born_inventory_preserves seed frame) belongs)
theorem scalar_inventory_next :
    ∀ event ∈ (updatedSeed seed (epoch frame) (Shared.actualOccurrence frame)).trace,
      event ∈ (updatedSeed seed (epoch (Shared.next frame (configuration seed)))
        (Shared.actualOccurrence (Shared.next frame (configuration seed)))).trace := by
  unfold Shared.next
  cases frame.action with
  | inr paid => exact InventoryProgramme.inventory_math_next seed frame
  | inl settled =>
      intro event belongs
      apply (SourceHistoryCommon.parallel_left _ _ _).1
      change event ∈ (SourceHistoryCommon.seed seed
        (Pair.relationWrite seed (epoch frame) (Shared.actualOccurrence frame)
          (Pair.disposition seed (epoch frame) (Shared.actualOccurrence frame)))).trace
      exact (SourceHistoryCommon.parallel_right _ _ _).1 event
        (Pair.relation_write_preserves seed (epoch frame) _ _ event belongs)

end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
