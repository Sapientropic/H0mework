import H0mework.Versions.V2.Arithmetic.FockUnitAction.Inventory.SourceSelected.Calculation.Cursor.Native.Feed.Continuation.Consumer
import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Environment
import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Completion.Births

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Continuation.Actor.Source
open SourceOperationEffects SourceOperationExecution
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (frames next nextBorn runtime)
end A
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment
  (At active epoch mathNext born_raw frames_constant)
end E
namespace B
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Births
  (birthIndex actual_action birthIndex_step actual_next actual_compiles)
end B
namespace F
export Cursor.Native.Feed.Source
  (Values Vars dynamicFeed updatedEnvironment updated_source_is_action programme)
end F
namespace C
export Continuation.Source (Frame continuous)
export Continuation.Consumer (born_environment programme_source)
end C
namespace N
export Cursor.Native.Source (canonical recover complete_inverse cursorRestriction cursor_restriction C.mathRuntime)
export Cursor.Native.Action (actualAction actualAction_source)
end N

def pointEnv (depth count clock : Nat) : Env (F.Values depth count) F.Vars :=
  fun slot _ => match slot with
  | false => N.canonical depth count (SourceOperationNative.point (N.C.mathRuntime depth clock))
  | true => 0

theorem initial_env (depth count : Nat) :
    E.At (F.dynamicFeed depth count) (pointEnv depth count (count + 1)) := by
  have computed : F.updatedEnvironment depth count = pointEnv depth count (count + 1) := by
    funext slot name
    cases slot with
    | false =>
        have source := F.updated_source_is_action depth count
        change F.updatedEnvironment depth count false Unit.unit = N.actualAction depth count
          (N.canonical depth count (SourceOperationNative.point (N.C.mathRuntime depth count))) at source
        rw [N.actualAction_source, SourceOperationNative.sourceAction_point] at source
        exact source
    | true => rfl
  exact fun {_current} _occurrence => computed

theorem born_env (depth count clock : Nat) (frame : C.Frame depth count)
    (same : E.At frame (pointEnv depth count clock)) :
    E.At (A.nextBorn frame (C.continuous depth count)) (pointEnv depth count (clock + 1)) := by
  intro current occurrence
  rw [C.born_environment, E.epoch same]
  funext slot name
  cases slot with
  | false =>
      change ((F.programme depth count).eval (pointEnv depth count clock)).1 = _
      rw [C.programme_source]
      change N.actualAction depth count
        (N.canonical depth count (SourceOperationNative.point (N.C.mathRuntime depth clock))) = _
      rw [N.actualAction_source, SourceOperationNative.sourceAction_point]
      rfl
  | true => rfl

abbrev frameAt (depth count stage : Nat) :=
  A.frames (F.dynamicFeed depth count) (C.continuous depth count) stage

/-- This counts actual native syntax visits, including visits after local actor completion. -/
def actorClock (depth count : Nat) : Nat → Nat
  | 0 => count + 1
  | stage + 1 => match (frameAt depth count stage).action with
    | .inl _ => actorClock depth count stage + 1
    | .inr _ => actorClock depth count stage

theorem frames_env (depth count stage : Nat) :
    E.At (frameAt depth count stage) (pointEnv depth count (actorClock depth count stage)) := by
  induction stage with
  | zero => exact initial_env depth count
  | succ stage previous =>
      change E.At (A.next (frameAt depth count stage) (C.continuous depth count))
        (pointEnv depth count (actorClock depth count (stage + 1)))
      unfold A.next
      simp only [actorClock]
      cases (frameAt depth count stage).action with
      | inl settled => exact born_env depth count _ _ previous
      | inr paid => exact E.mathNext previous

theorem actual_epoch_env (depth count stage : Nat) :
    (frameAt depth count stage).activeEnvironment = (A.epoch (frameAt depth count stage)).activeEnvironment :=
  (E.active (frames_env depth count stage)).trans (E.epoch (frames_env depth count stage)).symm

theorem actorClock_paid (depth count stage : Nat)
    {paid : DebtActivationWorld.GeneratedStepAt
      (RootGeneratedDebtActivationJointSource.Idle.law
        (frameAt depth count stage).registered.input.environment (frameAt depth count stage).registered.input.expression)
      (frameAt depth count stage).event.state}
    (actual : (frameAt depth count stage).action = .inr paid) :
    actorClock depth count (stage + 1) = actorClock depth count stage := by
  simp only [actorClock, actual]

theorem actorClock_step (depth count stage : Nat) :
    actorClock depth count stage ≤ actorClock depth count (stage + 1) := by
  simp only [actorClock]
  cases (frameAt depth count stage).action <;> simp only <;> omega
theorem actorClock_mono (depth count : Nat) : Monotone (actorClock depth count) :=
  monotone_nat_of_le_succ (actorClock_step depth count)

abbrev birth (depth count ordinal : Nat) :=
  B.birthIndex (C.continuous depth count) (F.dynamicFeed depth count) ordinal
theorem actorClock_birth (depth count ordinal : Nat) :
    actorClock depth count (birth depth count ordinal + 1) = actorClock depth count (birth depth count ordinal) + 1 := by
  simp only [actorClock]
  rw [B.actual_action]
theorem birthClock_step (depth count ordinal : Nat) :
    actorClock depth count (birth depth count ordinal) < actorClock depth count (birth depth count (ordinal + 1)) := by
  have times := B.birthIndex_step (C.continuous depth count) (F.dynamicFeed depth count) ordinal
  change birth depth count ordinal < birth depth count (ordinal + 1) at times
  have moves := actorClock_mono depth count (show birth depth count ordinal + 1 ≤ birth depth count (ordinal + 1) by omega)
  rw [actorClock_birth] at moves
  omega
theorem birthClock_lower (depth count ordinal : Nat) : ordinal ≤ actorClock depth count (birth depth count ordinal) := by
  induction ordinal with
  | zero => exact Nat.zero_le _
  | succ ordinal previous => have strict := birthClock_step depth count ordinal; omega

theorem birth_raw (depth count ordinal : Nat) :
    (frameAt depth count (birth depth count ordinal + 1)).rawRead.environment =
      pointEnv depth count (actorClock depth count (birth depth count ordinal)) := by
  have born : frameAt depth count (birth depth count ordinal + 1) =
      A.nextBorn (frameAt depth count (birth depth count ordinal)) (C.continuous depth count) := by
    change A.next _ _ = _
    unfold A.next
    rw [B.actual_action]
  rw [born]
  exact (E.born_raw (C.continuous depth count) (frameAt depth count (birth depth count ordinal))).trans
    (E.active (frames_env depth count (birth depth count ordinal)))

end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation.Cursor.Native.Feed.Continuation.Actor.Source
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
