import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.Acted.Consumer
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Consumer

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted.Inventory
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
 [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
abbrev pairStock := Residual.pairInventory seed (epoch frame) (Shared.actualOccurrence frame)

theorem prior_pair_preserved (prior) (hasPrior : frame.pairInventory=some prior) (event)
 (present : event ∈ prior.trace) : event ∈ (pairStock seed frame).trace := by
 apply (SourceHistoryCommon.parallel_left _ _ _).1
 unfold Residual.priorPairInventory
 rw [show (epoch frame).pairInventory=some prior from hasPrior]
 exact (SourceHistoryCommon.parallel_left _ _ _).1 event present

theorem written_pair_preserved (event) (present : event ∈ (pairStock seed frame).trace) :
 event ∈ (Past.written seed frame).trace :=
 Past.current_written_preserved seed frame event
  (Joint.complete_written_preserves seed (epoch frame) (Shared.actualOccurrence frame) event present)

theorem carried_pair_next (prior) (hasPrior : frame.pairInventory=some prior) (event)
 (present : event ∈ prior.trace) :
 ∃ carried, (Shared.next frame (programme seed)).pairInventory=some carried ∧ event ∈ carried.trace := by
 unfold Shared.next
 cases frame.action with
 | inr paid => exact ⟨prior,hasPrior,present⟩
 | inl settled =>
  refine ⟨_,rfl,?_⟩
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event
   (written_pair_preserved seed frame event (prior_pair_preserved seed frame prior hasPrior event present))

variable (initial : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
theorem full_carried_pair_inventory (prior) (hasPrior : initial.pairInventory=some prior)
 (distance : Nat) (event) (present : event ∈ prior.trace) :
 ∃ carried, (frameAt seed initial distance).pairInventory=some carried ∧ event ∈ carried.trace := by
 induction distance with
 | zero => exact ⟨prior,hasPrior,present⟩
 | succ distance previous =>
  obtain ⟨carried,hasCarried,member⟩ := previous
  exact carried_pair_next seed (frameAt seed initial distance) carried hasCarried event member

theorem full_pair_inventory (prior) (hasPrior : initial.pairInventory=some prior)
 (distance : Nat) (event) (present : event ∈ prior.trace) :
 event ∈ (pairStock seed (frameAt seed initial distance)).trace := by
 obtain ⟨carried,hasCarried,member⟩ := full_carried_pair_inventory seed initial prior hasPrior distance event present
 exact prior_pair_preserved seed (frameAt seed initial distance) carried hasCarried event member

end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted.Inventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
