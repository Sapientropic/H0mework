import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarInventoryLift
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (CofinalHistorySettlement.PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : Context.Installation.Occurrence frame (current:=current))
theorem birth_inventory_preserved : ∀ atom ∈ (updatedSeed seed (epoch frame) (Shared.actualOccurrence frame)).trace,
    atom ∈ (updatedSeed seed (epoch (Shared.nextBorn frame (configuration seed)))
      (Shared.actualOccurrence (Shared.nextBorn frame (configuration seed)))).trace := by
  intro atom belongs
  apply (SourceHistoryCommon.parallel_left _ _ _).1
  change atom ∈ (SourceHistoryCommon.seed seed (relationWrite seed (epoch frame) (Shared.actualOccurrence frame)
    (disposition seed (epoch frame) (Shared.actualOccurrence frame)))).trace
  apply (SourceHistoryCommon.parallel_right _ _ _).1
  exact relation_write_preserves seed (epoch frame) (Shared.actualOccurrence frame) _ atom belongs

theorem inventory_next : ∀ atom ∈ (updatedSeed seed (epoch frame) (Shared.actualOccurrence frame)).trace,
    atom ∈ (updatedSeed seed (epoch (Shared.next frame (configuration seed)))
      (Shared.actualOccurrence (Shared.next frame (configuration seed)))).trace := by
  unfold Shared.next
  cases frame.action with
  | inl settled => exact birth_inventory_preserved seed frame
  | inr paid => exact InventoryProgramme.inventory_math_next seed frame


def transition : CofinalHistoryTransition.GeneratedTransition
    (InventoryProgramme.history seed (epoch frame) (Shared.actualOccurrence frame))
    (InventoryProgramme.history seed (epoch (Shared.next frame (configuration seed)))
      (Shared.actualOccurrence (Shared.next frame (configuration seed)))) :=
  CofinalHistoryTransition.GeneratedTransition.create _ _
    (SourceOperationPaidRelations.generators_next _ _ _ _ (inventory_next seed frame)) (by
      intro word belongs
      change (InventoryProgramme.history seed (epoch (Shared.next frame (configuration seed)))
        (Shared.actualOccurrence (Shared.next frame (configuration seed)))).completionProjection
          ⟨word.val,SourceOperationPaidRelations.generators_next _ _ _ _ (inventory_next seed frame) word.property⟩ = 0
      apply (Submodule.Quotient.mk_eq_zero _).2
      exact SourceOperationPaidRelations.relations_next _ _ _ _ (inventory_next seed frame) belongs)
end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
