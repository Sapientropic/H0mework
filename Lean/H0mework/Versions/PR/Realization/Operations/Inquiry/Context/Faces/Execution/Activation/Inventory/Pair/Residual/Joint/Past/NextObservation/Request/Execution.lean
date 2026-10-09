import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.Source
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Packet
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
namespace J
export RootGeneratedDebtActivationJointSource (initialEvent mathAction)
export RootGeneratedDebtActivationJointSource.Successor (read? Packet join join_whole_paid)
end J
private theorem not_settled (settled : SourceOperationExecutionDebt.Settlement (J.initialEvent (registered seed frame)).state) : False := by
  have zero := (RootGeneratedDebtActivationJointSource.Idle.law (registered seed frame).input.environment
    (registered seed frame).input.expression).settlement_budget_zero settled
  have actualBudget := R.budget (actualMaterial seed frame)
  change remaining (R.expression (actualMaterial seed frame)) = 0 at zero
  omega

def firstStep := match _selected : J.mathAction (J.initialEvent (registered seed frame)) with
  | .inl settled => False.elim (not_settled seed frame settled)
  | .inr paid => paid

theorem firstStep_generated : J.mathAction (J.initialEvent (registered seed frame)) = .inr (firstStep seed frame) := by
  unfold firstStep
  cases selected : J.mathAction (J.initialEvent (registered seed frame)) with
  | inl settled => exact False.elim (not_settled seed frame settled)
  | inr paid => rfl

abbrev packets := RootGeneratedDebtActivationJointSource.OwnerFree.packetAt
  (old seed frame) (origin frame) (reader seed frame)

def root := RootGeneratedDebtActivationJointSource.Successor.Restructuring.livingRoot
  (calculationRoot seed frame) (registered seed frame) (packets seed frame)
def runtime := RootGeneratedDebtActivationJointSource.Successor.Restructuring.initialRuntime
  (calculationRoot seed frame) (registered seed frame) (packets seed frame)

theorem first_whole : type_of% (J.join_whole_paid (packets seed frame (endpoint seed frame))
    (J.initialEvent (registered seed frame)) (firstStep seed frame) (firstStep_generated seed frame)) :=
  J.join_whole_paid (packets seed frame (endpoint seed frame))
    (J.initialEvent (registered seed frame)) (firstStep seed frame) (firstStep_generated seed frame)

namespace T
export RootGeneratedDebtActivationJointSource.Successor.Restructuring
  (tick_math tick_next tick_full_destination tick_original_projection facade_tick_factorizes completeFace tickCertificate)
namespace C
export RootGeneratedDebtActivationJointSource.Successor.Restructuring.Calculation (completed completed_value completed_history)
end C
end T

theorem first_math : (RootGeneratedDebtActivationJointSource.Successor.Restructuring.runtimeCurrent
    (calculationRoot seed frame) (registered seed frame) (packets seed frame) (runtime seed frame).tick.next).2.state =
    (firstStep seed frame).1 := by
  apply (T.tick_math (calculationRoot seed frame) (registered seed frame) (packets seed frame) (runtime seed frame)).trans
  change RootGeneratedDebtActivationJointSource.mathTarget (J.initialEvent (registered seed frame)) = _
  unfold RootGeneratedDebtActivationJointSource.mathTarget
  rw [firstStep_generated]

theorem first_face : type_of% (T.facade_tick_factorizes (calculationRoot seed frame) (registered seed frame) (packets seed frame)
    (runtime seed frame) (T.completeFace (calculationRoot seed frame) (registered seed frame) (packets seed frame) (runtime seed frame)).projection) :=
  T.facade_tick_factorizes _ _ _ _ _

theorem full_old_inventory (projection : (calculationRoot seed frame).source.projectionLaw.Projection) :
    type_of% (T.tick_original_projection (calculationRoot seed frame) (registered seed frame) (packets seed frame)
      (runtime seed frame) projection) := T.tick_original_projection _ _ _ _ projection

theorem canonical_next : type_of% (T.tick_next (calculationRoot seed frame) (registered seed frame) (packets seed frame)
    (runtime seed frame)) := T.tick_next _ _ _ _

def completed := T.C.completed (calculationRoot seed frame) (registered seed frame) (packets seed frame)

theorem terminal_effect : (completed seed frame).1 =
    effectEvaluator (R:=ℤ) (actualMaterial seed frame).environment (actualMaterial seed frame).increment
      (SourceOperationScalarPresentation.relationMap (R:=ℤ) (actualMaterial seed frame).environment
        (R.relations (R:=ℤ) (actualMaterial seed frame))) :=
  (T.C.completed_value (calculationRoot seed frame) (registered seed frame) (packets seed frame)).trans (effect_generated seed frame)

theorem terminal_inverse : (SourceGeneratedScalarDifferentialResidual.residualEquivRange
    (evaluation (R:=ℤ) (registered seed frame).input.environment)
    (SourceGeneratedScalarDifferentialResidual.canonicalResidual (evaluation (R:=ℤ) (registered seed frame).input.environment)
      (SourceOperationScalarPresentation.relationMap (R:=ℤ) (actualMaterial seed frame).environment
        (R.relations (R:=ℤ) (actualMaterial seed frame))))).val = (completed seed frame).1 :=
  (inverse_generated seed frame).trans
    (T.C.completed_value (calculationRoot seed frame) (registered seed frame) (packets seed frame)).symm

abbrev completedState :=
  (RootGeneratedDebtActivationJointSource.Successor.Restructuring.runtimeCurrent
    (calculationRoot seed frame) (registered seed frame) (packets seed frame)
    (RootGeneratedDebtActivationJointSource.Successor.Restructuring.Calculation.targetRuntime
      (calculationRoot seed frame) (registered seed frame) (packets seed frame))).2.state
abbrev exposure := SourceOperationPaidRelations.exposure (completedState seed frame).2
abbrev written := SourceHistoryCommon.seed (Past.written seed frame) (exposure seed frame)
theorem complete_trace (event : PresentedRelationEventAt (Expr (PairValue PhysicalValue) PhysicalVar sort))
    (present : event ∈ (exposure seed frame).trace) : event ∈ (written seed frame).trace :=
  (SourceHistoryCommon.parallel_right _ _ _).1 event present
theorem old_written (event : PresentedRelationEventAt (Expr (PairValue PhysicalValue) PhysicalVar sort))
    (present : event ∈ (Past.written seed frame).trace) : event ∈ (written seed frame).trace :=
  (SourceHistoryCommon.parallel_left _ _ _).1 event present
theorem completed_history : (completedState seed frame).2.length = remaining (registered seed frame).input.expression :=
  RootGeneratedDebtActivationJointSource.Successor.Restructuring.Calculation.completed_history
    (calculationRoot seed frame) (registered seed frame) (packets seed frame)

def configuration := {continuedConfiguration seed with
  nextPairInventory := fun sourceFrame => some (written seed sourceFrame)}
theorem actual_born_inventory : (Shared.nextBorn frame (configuration seed)).pairInventory =
    some (written seed frame) := rfl
theorem all_trace_born (event : PresentedRelationEventAt (Expr (PairValue PhysicalValue) PhysicalVar sort))
    (present : event ∈ (exposure seed frame).trace) :
    event ∈ (written seed frame).trace := complete_trace seed frame event present

theorem shared_next_environment :
    (Shared.next frame (configuration seed)).rawRead.environment =
      (Shared.next frame (continuedConfiguration seed)).rawRead.environment := by
  unfold Shared.next
  cases frame.action with
  | inr paid => rfl
  | inl settled =>
      exact (Shared.nextBorn frame (configuration seed)).raw_environment.trans
        ((show (Shared.nextBorn frame (configuration seed)).registered.input.environment =
          (Shared.nextBorn frame (continuedConfiguration seed)).registered.input.environment from rfl).trans
          (Shared.nextBorn frame (continuedConfiguration seed)).raw_environment.symm)

theorem shared_current_raw : (Shared.query frame (configuration seed)).raw =
    (Shared.query frame (continuedConfiguration seed)).raw := by
  change queryRaw seed (epoch frame) (Shared.actualOccurrence frame)
      (disposition seed (epoch frame) (Shared.actualOccurrence frame)) = _
  rfl

end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
