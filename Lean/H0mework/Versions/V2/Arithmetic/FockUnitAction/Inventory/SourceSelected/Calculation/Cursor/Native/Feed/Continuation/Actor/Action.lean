import H0mework.Versions.V2.Arithmetic.FockUnitAction.Inventory.SourceSelected.Calculation.Cursor.Native.Feed.Continuation.Actor.Source
import H0mework.Versions.V2.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Frame.Environment
import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Environment.Increment

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Continuation.Actor.Action
open SourceOperationEffects SourceOperationExecution
namespace S
export NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Continuation.Actor.Source
  (pointEnv frameAt actorClock frames_env actorClock_paid actorClock_birth actorClock_mono)
end S
namespace F
export NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Source
  (environment dynamicFeed Values Vars)
end F
namespace C
export NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Continuation.Source
  (continuous)
end C
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (next nextBorn runtime frames)
end A
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment (At active born_raw)
end E
namespace N
export NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Source
  (canonical C.mathRuntime)
export NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Action
  (actualAction actualEffect coimageBackward actualAction_source coimage_backward_action)
end N


private theorem actorClock_positive (depth count stage : Nat) : 0 < S.actorClock depth count stage := by
  have previous := S.actorClock_mono depth count (Nat.zero_le stage)
  change count + 1 ≤ S.actorClock depth count stage at previous
  omega

theorem raw_env (depth count stage : Nat) :
    (S.frameAt depth count stage).rawRead.environment =
      S.pointEnv depth count (S.actorClock depth count stage - 1) := by
  induction stage with
  | zero =>
      rw [RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.raw_environment]
      change _ = S.pointEnv depth count ((count + 1) - 1)
      rw [Nat.add_sub_cancel]
      have original := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.Environment.raw_environment (N.C.mathRuntime depth count).current.root
        (N.C.mathRuntime depth count).current.visit (NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Source.sourceU7 depth) (NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Source.sourceCalculus depth) (NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Source.reader depth count)
      exact original
  | succ stage previous =>
      change (A.next (S.frameAt depth count stage) (C.continuous depth count)).rawRead.environment = _
      unfold A.next
      cases selected : (S.frameAt depth count stage).action with
      | inr paid =>
          rw [S.actorClock_paid depth count stage selected]
          exact previous
      | inl settled =>
          rw [E.born_raw]
          rw [E.active (S.frames_env depth count stage)]
          have clock : S.actorClock depth count (stage + 1) = S.actorClock depth count stage + 1 := by
            simp only [S.actorClock, selected]
          rw [clock]
          change S.pointEnv depth count (S.actorClock depth count stage) =
            S.pointEnv depth count ((S.actorClock depth count stage + 1) - 1)
          simp only [Nat.add_sub_cancel]

theorem action_raw_active (depth count stage : Nat) :
    N.actualAction depth count ((S.frameAt depth count stage).rawRead.environment false Unit.unit) =
      (S.frameAt depth count stage).activeEnvironment false Unit.unit := by
  rw [raw_env, E.active (S.frames_env depth count stage)]
  change N.actualAction depth count
      (N.canonical depth count (SourceOperationNative.point (N.C.mathRuntime depth (S.actorClock depth count stage - 1)))) =
    N.canonical depth count (SourceOperationNative.point (N.C.mathRuntime depth (S.actorClock depth count stage)))
  rw [N.actualAction_source, SourceOperationNative.sourceAction_point]
  have clock : S.actorClock depth count stage - 1 + 1 = S.actorClock depth count stage := by
    have positive := actorClock_positive depth count stage
    omega
  change N.canonical depth count (SourceOperationNative.point (N.C.mathRuntime depth (S.actorClock depth count stage - 1 + 1))) = _
  rw [clock]

namespace O
export SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation
 (rawSource)
end O
abbrev runtime (depth count : Nat) := A.runtime (F.dynamicFeed depth count) (C.continuous depth count)
abbrev rawSource (depth count : Nat) := O.rawSource (F.dynamicFeed depth count) (C.continuous depth count)

theorem increment_branch (depth count stage : Nat) : type_of%
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.Increment.actual
      (C.continuous depth count) (F.dynamicFeed depth count) stage) :=
  SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.Increment.actual
    (C.continuous depth count) (F.dynamicFeed depth count) stage

theorem native_increment (depth count stage : Nat) :
    (SourceOperationInquiry.Context.increment (runtime depth count) (rawSource depth count)
      ((runtime depth count).stateAt stage)) false Unit.unit =
    match (S.frameAt depth count stage).action with
    | .inl _ => N.actualEffect depth count ((S.frameAt depth count stage).rawRead.environment false Unit.unit)
    | .inr _ => 0 := by
  rw [increment_branch]
  cases (S.frameAt depth count stage).action with
  | inl settled =>
      change (S.frameAt depth count stage).activeEnvironment false Unit.unit -
        (S.frameAt depth count stage).rawRead.environment false Unit.unit = _
      rw [← action_raw_active]
      rfl
  | inr paid => rfl

theorem raw_inverse (depth count stage : Nat) :
    N.coimageBackward depth count ((S.frameAt depth count stage).activeEnvironment false Unit.unit) =
      (S.frameAt depth count stage).rawRead.environment false Unit.unit := by
  rw [← action_raw_active, raw_env]
  exact N.coimage_backward_action depth count _

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Continuation.Actor.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
