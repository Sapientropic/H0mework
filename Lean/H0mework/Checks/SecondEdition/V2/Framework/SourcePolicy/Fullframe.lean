import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Native.Frame.Source
import H0mework.Versions.V2.Arithmetic.FockUnitAction.Inventory.SourceSelected.Calculation.Cursor.Native.Feed.Continuation.Actor.Action
import H0mework.Versions.PR.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Clock

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePolicyFullFrameControls
namespace F
export SourceOperationInquiry.Context.Native.Frame
  (observer model_next inventory_next paid_depth_next model_ne_next)
end F
namespace S
export NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Continuation.Actor.Source
  (F.dynamicFeed C.continuous frameAt birth B.actual_action A.next A.nextBorn)
end S
namespace D
export NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Continuation.Actor.Action
  (runtime rawSource increment_branch native_increment N.actualEffect)
end D
namespace Q
export SourceOperationInquiry.Context
  (completionEnvironment completionAction completionPoint readCompletion readEnv increment
   actual_next_environment actual_operation_receipt completion_same_typed)
end Q

theorem full_current_next (depth count stage : Nat) : type_of%
    (F.model_next (S.F.dynamicFeed depth count) (S.C.continuous depth count) stage) :=
  F.model_next (S.F.dynamicFeed depth count) (S.C.continuous depth count) stage

theorem full_actual_inventory (depth count stage : Nat) : type_of%
    (F.inventory_next (S.F.dynamicFeed depth count) (S.C.continuous depth count) stage) :=
  F.inventory_next (S.F.dynamicFeed depth count) (S.C.continuous depth count) stage

theorem actual_macro_effect (depth count stage : Nat) :
    (Q.completionEnvironment (D.runtime depth count) (D.rawSource depth count)
      (Q.completionAction (D.runtime depth count)
        (Q.completionPoint (D.runtime depth count) ((D.runtime depth count).stateAt stage)))) false Unit.unit -
      (Q.readEnv (D.runtime depth count) (D.rawSource depth count) ((D.runtime depth count).stateAt stage)) false Unit.unit =
    match (S.frameAt depth count stage).action with
    | .inl _ => D.N.actualEffect depth count ((S.frameAt depth count stage).rawRead.environment false Unit.unit)
    | .inr _ => 0 := by
  rw [Q.actual_next_environment]
  change (Q.increment (D.runtime depth count) (D.rawSource depth count) ((D.runtime depth count).stateAt stage)) false Unit.unit = _
  exact D.native_increment depth count stage

theorem actual_receipt (depth count stage : Nat) : type_of%
    (Q.actual_operation_receipt (D.runtime depth count) (D.rawSource depth count) ((D.runtime depth count).stateAt stage)) :=
  Q.actual_operation_receipt (D.runtime depth count) (D.rawSource depth count) ((D.runtime depth count).stateAt stage)

theorem same_source_next (depth count stage : Nat) : type_of%
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_next
      (S.F.dynamicFeed depth count) (S.C.continuous depth count) stage) :=
  SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_next
    (S.F.dynamicFeed depth count) (S.C.continuous depth count) stage

theorem typed_phase_preserved (depth count : Nat) (first second : (D.runtime depth count).State)
    (same : Q.completionPoint (D.runtime depth count) first = Q.completionPoint (D.runtime depth count) second) :
    type_of% (Q.completion_same_typed (D.runtime depth count) first second same) :=
  Q.completion_same_typed (D.runtime depth count) first second same

private theorem born_frame (depth count ordinal : Nat) :
    S.frameAt depth count (S.birth depth count ordinal + 1) =
      S.A.nextBorn (S.frameAt depth count (S.birth depth count ordinal)) (S.C.continuous depth count) := by
  change S.A.next _ _ = _
  unfold S.A.next
  rw [S.B.actual_action]

theorem actual_paid_after_birth (depth count ordinal : Nat) :
    ∃ paid, (S.frameAt depth count (S.birth depth count ordinal + 1)).action = .inr paid := by
  rw [born_frame]
  let frame := S.frameAt depth count (S.birth depth count ordinal)
  let born := S.A.nextBorn frame (S.C.continuous depth count)
  change ∃ paid, born.action = .inr paid
  have budget := SourceRegisteredClaimClock.remainder_generated born
  change SourceOperationExecution.remaining born.event.state.1 =
    SourceOperationExecution.remaining frame.request.input.expression - 1 at budget
  have growth := frame.request_budget
  have positive : 0 < SourceOperationExecution.remaining born.event.state.1 := by omega
  cases born.action with
  | inr paid => exact ⟨paid, rfl⟩
  | inl settled =>
      have zero : SourceOperationExecution.remaining born.event.state.1 = 0 := by rw [settled.2.down]; rfl
      omega

theorem actual_paid_depth (depth count ordinal : Nat) :
    (F.observer (S.F.dynamicFeed depth count) (S.C.continuous depth count)
      (Q.readCompletion (D.runtime depth count) (Q.completionAction (D.runtime depth count)
        (Q.completionPoint (D.runtime depth count) ((D.runtime depth count).stateAt (S.birth depth count ordinal + 1)))))).mapDomain
      (fun frame => frame.depth) = Finsupp.single ((S.frameAt depth count (S.birth depth count ordinal + 1)).depth + 1) 1 := by
  rcases actual_paid_after_birth depth count ordinal with ⟨paid, actual⟩
  exact F.paid_depth_next (S.F.dynamicFeed depth count) (S.C.continuous depth count) _ actual

theorem paid_faithful_fibre (depth count stage : Nat)
    {paid : DebtActivationWorld.GeneratedStepAt
      (RootGeneratedDebtActivationJointSource.Idle.law
        (S.frameAt depth count stage).registered.input.environment (S.frameAt depth count stage).registered.input.expression)
      (S.frameAt depth count stage).event.state}
    (actual : (S.frameAt depth count stage).action = .inr paid) :
    Q.readEnv (D.runtime depth count) (D.rawSource depth count) ((D.runtime depth count).stateAt (stage + 1)) =
      Q.readEnv (D.runtime depth count) (D.rawSource depth count) ((D.runtime depth count).stateAt stage) ∧
    Q.completionPoint (D.runtime depth count) ((D.runtime depth count).stateAt stage) ≠
      Q.completionPoint (D.runtime depth count) ((D.runtime depth count).stateAt (stage + 1)) := by
  have effect := D.increment_branch depth count stage
  rw [actual] at effect
  change Q.readEnv (D.runtime depth count) (D.rawSource depth count) ((D.runtime depth count).stateAt (stage + 1)) -
    Q.readEnv (D.runtime depth count) (D.rawSource depth count) ((D.runtime depth count).stateAt stage) = 0 at effect
  exact ⟨sub_eq_zero.mp effect, F.model_ne_next (S.F.dynamicFeed depth count) (S.C.continuous depth count) stage⟩

theorem actual_paid_fibre (depth count ordinal : Nat) :
    Q.readEnv (D.runtime depth count) (D.rawSource depth count) ((D.runtime depth count).stateAt ((S.birth depth count ordinal + 1) + 1)) =
      Q.readEnv (D.runtime depth count) (D.rawSource depth count) ((D.runtime depth count).stateAt (S.birth depth count ordinal + 1)) ∧
    Q.completionPoint (D.runtime depth count) ((D.runtime depth count).stateAt (S.birth depth count ordinal + 1)) ≠
      Q.completionPoint (D.runtime depth count) ((D.runtime depth count).stateAt ((S.birth depth count ordinal + 1) + 1)) := by
  rcases actual_paid_after_birth depth count ordinal with ⟨paid, actual⟩
  exact paid_faithful_fibre depth count _ actual

#print axioms SourceOperationInquiry.Context.Native.Frame.fullword_read
#print axioms SourceOperationInquiry.Context.Native.Frame.model_next
#print axioms SourceOperationInquiry.Context.Native.Frame.inventory_next
#print axioms SourceOperationInquiry.Context.Native.Frame.paid_depth_next
#print axioms full_current_next
#print axioms full_actual_inventory
#print axioms actual_macro_effect
#print axioms actual_receipt
#print axioms same_source_next
#print axioms typed_phase_preserved
#print axioms actual_paid_after_birth
#print axioms actual_paid_depth
#print axioms paid_faithful_fibre
#print axioms actual_paid_fibre
end SourcePolicyFullFrameControls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
