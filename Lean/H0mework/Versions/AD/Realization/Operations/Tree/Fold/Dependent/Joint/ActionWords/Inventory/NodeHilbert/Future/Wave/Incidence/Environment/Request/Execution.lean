import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.Request.Source
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Packet
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceContentEnvironment"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Request
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarInventoryLift CofinalHistorySettlement
variable (frame : Frame.{u})
namespace J
export RootGeneratedDebtActivationJointSource (initialEvent mathAction)
export RootGeneratedDebtActivationJointSource.Successor (read? Packet join join_whole_paid)
end J
private theorem not_settled (settled : SourceOperationExecutionDebt.Settlement (J.initialEvent (registered frame)).state) : False := by
  have zero := (RootGeneratedDebtActivationJointSource.Idle.law (registered frame).input.environment
    (registered frame).input.expression).settlement_budget_zero settled
  have actualBudget := R.budget (actualMaterial frame)
  change remaining (R.expression (actualMaterial frame)) = 0 at zero
  omega

def firstStep := match _selected : J.mathAction (J.initialEvent (registered frame)) with
  | .inl settled => False.elim (not_settled frame settled)
  | .inr paid => paid

theorem firstStep_generated : J.mathAction (J.initialEvent (registered frame)) = .inr (firstStep frame) := by
  unfold firstStep
  cases selected : J.mathAction (J.initialEvent (registered frame)) with
  | inl settled => exact False.elim (not_settled frame settled)
  | inr paid => rfl

abbrev packets := RootGeneratedDebtActivationJointSource.OwnerFree.packetAt
  (old frame) (origin frame) (reader frame)

def root := RootGeneratedDebtActivationJointSource.Successor.Restructuring.livingRoot
  (calculationRoot frame) (registered frame) (packets frame)
def runtime := RootGeneratedDebtActivationJointSource.Successor.Restructuring.initialRuntime
  (calculationRoot frame) (registered frame) (packets frame)

theorem first_whole : type_of% (J.join_whole_paid (packets frame (endpoint frame))
    (J.initialEvent (registered frame)) (firstStep frame) (firstStep_generated frame)) :=
  J.join_whole_paid (packets frame (endpoint frame))
    (J.initialEvent (registered frame)) (firstStep frame) (firstStep_generated frame)

namespace T
export RootGeneratedDebtActivationJointSource.Successor.Restructuring
  (tick_math tick_next tick_full_destination tick_original_projection facade_tick_factorizes completeFace tickCertificate)
namespace C
export RootGeneratedDebtActivationJointSource.Successor.Restructuring.Calculation (completed completed_value completed_history)
end C
end T

theorem first_math : (RootGeneratedDebtActivationJointSource.Successor.Restructuring.runtimeCurrent
    (calculationRoot frame) (registered frame) (packets frame) (runtime frame).tick.next).2.state =
    (firstStep frame).1 := by
  apply (T.tick_math (calculationRoot frame) (registered frame) (packets frame) (runtime frame)).trans
  change RootGeneratedDebtActivationJointSource.mathTarget (J.initialEvent (registered frame)) = _
  unfold RootGeneratedDebtActivationJointSource.mathTarget
  rw [firstStep_generated]

theorem first_face : type_of% (T.facade_tick_factorizes (calculationRoot frame) (registered frame) (packets frame)
    (runtime frame) (T.completeFace (calculationRoot frame) (registered frame) (packets frame) (runtime frame)).projection) :=
  T.facade_tick_factorizes _ _ _ _ _

theorem full_old_inventory (projection : (calculationRoot frame).source.projectionLaw.Projection) :
    type_of% (T.tick_original_projection (calculationRoot frame) (registered frame) (packets frame)
      (runtime frame) projection) := T.tick_original_projection _ _ _ _ projection

theorem canonical_next : type_of% (T.tick_next (calculationRoot frame) (registered frame) (packets frame)
    (runtime frame)) := T.tick_next _ _ _ _

def completed := T.C.completed (calculationRoot frame) (registered frame) (packets frame)

theorem terminal_effect : (completed frame).1 =
    effectEvaluator (R:=ℤ) (actualMaterial frame).environment (actualMaterial frame).increment
      (SourceOperationScalarPresentation.relationMap (R:=ℤ) (actualMaterial frame).environment
        (R.relations (R:=ℤ) (actualMaterial frame))) :=
  (T.C.completed_value (calculationRoot frame) (registered frame) (packets frame)).trans (effect_generated frame)

theorem terminal_inverse : (SourceGeneratedScalarDifferentialResidual.residualEquivRange
    (evaluation (R:=ℤ) (registered frame).input.environment)
    (SourceGeneratedScalarDifferentialResidual.canonicalResidual (evaluation (R:=ℤ) (registered frame).input.environment)
      (SourceOperationScalarPresentation.relationMap (R:=ℤ) (actualMaterial frame).environment
        (R.relations (R:=ℤ) (actualMaterial frame))))).val = (completed frame).1 :=
  (inverse_generated frame).trans
    (T.C.completed_value (calculationRoot frame) (registered frame) (packets frame)).symm

abbrev completedState :=
  (RootGeneratedDebtActivationJointSource.Successor.Restructuring.runtimeCurrent
    (calculationRoot frame) (registered frame) (packets frame)
    (RootGeneratedDebtActivationJointSource.Successor.Restructuring.Calculation.targetRuntime
      (calculationRoot frame) (registered frame) (packets frame))).2.state
abbrev exposure := SourceOperationPaidRelations.exposure (completedState frame).2
abbrev written := SourceHistoryCommon.seed (Disposition.completeWritten (A.epoch frame) (Shared.actualOccurrence frame)) (exposure frame)
theorem complete_trace (event : PresentedRelationEventAt (Expr (PairValue Value.{u}) Var.{u} Slot.orbit))
    (present : event ∈ (exposure frame).trace) : event ∈ (written frame).trace :=
  (SourceHistoryCommon.parallel_right _ _ _).1 event present
theorem old_written (event : PresentedRelationEventAt (Expr (PairValue Value.{u}) Var.{u} Slot.orbit))
    (present : event ∈ (Disposition.completeWritten (A.epoch frame) (Shared.actualOccurrence frame)).trace) : event ∈ (written frame).trace :=
  (SourceHistoryCommon.parallel_left _ _ _).1 event present
theorem completed_history : (completedState frame).2.length = remaining (registered frame).input.expression :=
  RootGeneratedDebtActivationJointSource.Successor.Restructuring.Calculation.completed_history
    (calculationRoot frame) (registered frame) (packets frame)

def configuration := {Disposition.programme.{u} with
  nextPairInventory := fun sourceFrame => some (written sourceFrame)}
theorem actual_born_inventory : (Shared.nextBorn frame configuration).pairInventory =
    some (written frame) := rfl
theorem all_trace_born (event : PresentedRelationEventAt (Expr (PairValue Value.{u}) Var.{u} Slot.orbit))
    (present : event ∈ (exposure frame).trace) :
    event ∈ (written frame).trace := complete_trace frame event present

theorem shared_next_environment :
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next frame configuration).rawRead.environment =
      (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next frame Disposition.programme).rawRead.environment := by
  unfold SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
  cases frame.action with
  | inr paid => rfl
  | inl settled =>
      exact (Shared.nextBorn frame configuration).raw_environment.trans
        ((show (Shared.nextBorn frame configuration).registered.input.environment =
          (Shared.nextBorn frame Disposition.programme).registered.input.environment from rfl).trans
          (Shared.nextBorn frame Disposition.programme).raw_environment.symm)

theorem shared_current_raw : (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame configuration).raw =
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame Disposition.programme).raw := by
  change Disposition.queryRaw (A.epoch frame) (Shared.actualOccurrence frame)
      (Disposition.selected (A.epoch frame) (Shared.actualOccurrence frame)) = _
  rfl

end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Request
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
