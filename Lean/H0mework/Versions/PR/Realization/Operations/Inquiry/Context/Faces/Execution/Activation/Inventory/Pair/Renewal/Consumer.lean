import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Renewal.Source
import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Source
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Restructuring.Calculation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Renewal
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarInventoryLift
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (CofinalHistorySettlement.PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (frame : M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : Context.Installation.Occurrence frame (current:=current))

namespace I
export SourceOperationInquiry.Context.Native.Orbit.Installation (ofFrame frame_next)
end I

theorem cursor_shared_next (configuration : Programme (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=sort))
    (inherited : (Shared.datum frame configuration).nextEnvironmentRead = none)
    (inheritedAt : (Shared.datum frame configuration).nextEnvironmentReadAt = none) :
    (I.ofFrame frame).next = I.ofFrame (Shared.next frame configuration) := by
  have actionEq : (I.ofFrame frame).action = frame.action := rfl
  unfold Context.Native.Orbit.Installation.Cursor.next
  rw [actionEq]
  unfold Shared.next
  cases frame.action with
  | inr paid => rfl
  | inl settled =>
      unfold Shared.nextBorn
      simp only [inheritedAt,inherited]
      rfl

theorem second_environment_actual :
    Action.secondEnvironment frame (Shared.actualOccurrence frame) =
      (Shared.next (Shared.next frame (programme seed)) (programme seed)).rawRead.environment := by
  change ((I.ofFrame frame).next.next).raw.environment = _
  rw [cursor_shared_next frame (programme seed) rfl rfl,cursor_shared_next (Shared.next frame (programme seed)) (programme seed) rfl rfl]
  rfl

theorem first_environment_actual : Action.sourceNextEnvironment frame (Shared.actualOccurrence frame) =
    (Shared.next frame (programme seed)).rawRead.environment := by
  have first := Context.Installation.next_raw_source frame
  have rawEq : frame.next.rawRead = (Shared.next frame (programme seed)).rawRead := by
    unfold RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.next
      RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.nextFrom Shared.next
    cases frame.action <;> rfl
  exact (congrArg (fun raw => raw.environment) first).trans (congrArg (fun raw => raw.environment) rawEq)


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
  (T.C.completed_value (calculationRoot seed frame) (registered seed frame) (packets seed frame)).trans (completed_effect seed frame)

theorem terminal_inverse : (SourceGeneratedScalarDifferentialResidual.residualEquivRange
    (evaluation (R:=ℤ) (registered seed frame).input.environment)
    (SourceGeneratedScalarDifferentialResidual.canonicalResidual (evaluation (R:=ℤ) (registered seed frame).input.environment)
      (SourceOperationScalarPresentation.relationMap (R:=ℤ) (actualMaterial seed frame).environment
        (R.relations (R:=ℤ) (actualMaterial seed frame))))).val = (completed seed frame).1 :=
  (inverse_read seed frame).trans
    (T.C.completed_value (calculationRoot seed frame) (registered seed frame) (packets seed frame)).symm


theorem updated_pair_actual : (registered seed frame).input.environment =
    pairEnvironment (Shared.next frame (programme seed)).rawRead.environment
      ((Shared.next (Shared.next frame (programme seed)) (programme seed)).rawRead.environment -
        (Shared.next frame (programme seed)).rawRead.environment) := by
  apply (environment_source seed frame).trans
  change Action.updatedPairEnvironment (epoch frame) (Shared.actualOccurrence frame) = _
  have first : Action.sourceNextEnvironment (epoch frame) (Shared.actualOccurrence frame) =
      (Shared.next frame (programme seed)).rawRead.environment := by
    have same : Action.sourceNextEnvironment (epoch frame) (Shared.actualOccurrence frame) =
        Action.sourceNextEnvironment frame (Shared.actualOccurrence frame) := by
      unfold Action.sourceNextEnvironment InventoryProgramme.physical Context.Installation.materialAt
      dsimp only [epoch]
      rcases Shared.actualOccurrence frame with ⟨support,event⟩
      cases event
      unfold Context.Installation.nextRawAt Context.Installation.rawAt Context.Installation.residualAt
      cases RootGeneratedDebtActivationJointSource.mathAction (Shared.actualVisit frame).current.2 <;> rfl
    exact same.trans (first_environment_actual seed frame)
  have second : Action.secondEnvironment (epoch frame) (Shared.actualOccurrence frame) =
      (Shared.next (Shared.next frame (programme seed)) (programme seed)).rawRead.environment := by
    change Action.secondEnvironment frame (Shared.actualOccurrence frame) = _
    exact second_environment_actual seed frame
  exact congrArg₂ pairEnvironment first (congrArg₂ (· - ·) second first)

end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Renewal
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
