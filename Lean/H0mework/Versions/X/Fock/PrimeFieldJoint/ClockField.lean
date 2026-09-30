import H0mework.Versions.X.Fock.SourceHistoryClock.ComplexSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedJointClock

open SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open SourceGeneratedActionWords.Fock.OriginalHilbert SourceGeneratedAcquisitionMeasure SourceGeneratedJointTime
open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def signal (bound : Nat) (index : Fin (bound + 1)) : ℂ :=
  (SourceClockModel.rawClock (runtimeAt index.val).state : ℂ)

def nextSignal (bound : Nat) (index : Fin (bound + 1)) : ℂ :=
  (SourceClockModel.rawClock (runtimeAt index.val).tick.next.state : ℂ)

theorem signal_model (bound : Nat) (index : Fin (bound + 1)) :
    signal bound index = (SourceClockModel.clockRead (SourceClockModel.Fock.point index.val) : ℂ) := by
  exact congrArg (fun value : ℤ => (value : ℂ))
    (SourceOperationNative.Observed.modelPoint_read (process := process)
      SourceClockModel.rawClock (runtimeAt index.val)).symm

theorem signal_value (bound : Nat) (index : Fin (bound + 1)) :
    signal bound index = (index.val : ℂ) + 1 := by
  simp only [signal, runtimeAt_state, SourceClockModel.rawClock, Int.cast_add,
    Int.cast_natCast, Int.cast_one]

theorem signal_increment (bound : Nat) (index : Fin (bound + 1)) :
    nextSignal bound index = signal bound index + 1 := by
  change (SourceClockModel.rawClock (runtimeAt index.val).tick.next.state : ℂ) = _
  rw [next_address]
  simpa only [signal, runtimeAt_state] using SourceClockComplex.native_increment index.val

def currentClock (depth bound : Nat) : FieldSpace depth bound :=
  Actor.currentTransfer depth bound (taskValue (historyPMF bound) (signal bound))

def nextClock (depth bound : Nat) : NextSpace depth bound :=
  IsometricRetainedTransfer.transfer (Actor.nextPullback depth bound)
    (taskValue (historyPMF bound) (nextSignal bound))

def nextOne (depth bound : Nat) : NextSpace depth bound :=
  IsometricRetainedTransfer.transfer (Actor.nextPullback depth bound)
    (taskValue (historyPMF bound) (fun _ => 1))

private theorem task_increment (bound : Nat) :
    taskValue (historyPMF bound) (nextSignal bound) =
      taskValue (historyPMF bound) (signal bound) + taskValue (historyPMF bound) (fun _ => 1) := by
  apply MeasureTheory.Lp.ext
  apply Filter.Eventually.of_forall
  intro index
  have supported := SourceUniformFibreVariance.source_positive bound index
  have addition := ae_at_support (historyPMF bound) index supported
    (MeasureTheory.Lp.coeFn_add (taskValue (historyPMF bound) (signal bound))
      (taskValue (historyPMF bound) (fun _ => 1)))
  rw [addition]
  simp only [Pi.add_apply, taskValue_at _ _ index supported, signal_increment]

theorem original_time_increment (depth bound : Nat) :
    nextClock depth bound = timeTransfer depth bound (currentClock depth bound) + nextOne depth bound := by
  unfold nextClock
  rw [task_increment, map_add]
  congr 1
  exact DFunLike.congr_fun
    (IsometricRetainedTransfer.transfer_comp (Actor.currentPullback depth bound)
      (timePullback depth bound)) _

private theorem next_transfer_samples (depth bound : Nat) (value : SourceWeightedRecovery.Space (historyPMF bound)) :
    Actor.nextPullback depth bound (IsometricRetainedTransfer.transfer (Actor.nextPullback depth bound) value) = value := by
  rw [IsometricRetainedTransfer.transfer_comp]
  change Actor.nextPullback depth bound (timeTransfer depth bound (Actor.currentTransfer depth bound value)) = _
  have square := DFunLike.congr_fun (SourceGeneratedRecordFrame.joint_action_square depth bound)
    (Actor.currentTransfer depth bound value)
  exact square.trans (actor_transfer_samples depth bound _)

theorem next_clock_samples (depth bound : Nat) :
    Actor.nextPullback depth bound (nextClock depth bound) =
      taskValue (historyPMF bound) (nextSignal bound) := next_transfer_samples depth bound _

theorem next_clock_actual (depth bound : Nat) (index : Fin (bound + 1)) :
    nextClock depth bound (Actor.nextRead depth bound index) = nextSignal bound index := by
  have sample := congrArg (fun value : SourceWeightedRecovery.Space (historyPMF bound) => value index)
    (next_clock_samples depth bound)
  rw [Actor.nextPullback_at, taskValue_at _ _ index (SourceUniformFibreVariance.source_positive bound index)] at sample
  exact sample

theorem original_clock_recovery (depth bound : Nat) (index : Fin (bound + 1)) :
    timeTransfer depth bound (currentClock depth bound) (Actor.nextRead depth bound index) = signal bound index :=
  original_next_recovery depth bound (signal bound) index

theorem actual_clock_error (depth bound : Nat) (index : Fin (bound + 1)) :
    nextClock depth bound (Actor.nextRead depth bound index) -
      timeTransfer depth bound (currentClock depth bound) (Actor.nextRead depth bound index) = 1 := by
  rw [next_clock_actual, original_clock_recovery, signal_increment]
  ring

theorem next_one_norm_sq (depth bound : Nat) : ‖nextOne depth bound‖ ^ 2 = 1 := by
  rw [← (Actor.nextPullback depth bound).norm_map, nextOne, next_transfer_samples, norm_source_sq]
  simp only [taskValue_at _ _ _ (SourceUniformFibreVariance.source_positive _ _), norm_one, one_pow, mul_one,
    SourceUniformFibreVariance.source_weight, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  have positive : (bound + 1 : ℝ) ≠ 0 := by positivity
  field_simp

theorem original_clock_error_norm (depth bound : Nat) :
    ‖nextClock depth bound - timeTransfer depth bound (currentClock depth bound)‖ ^ 2 = 1 := by
  rw [original_time_increment, add_sub_cancel_left, next_one_norm_sq]

theorem original_adjusted_recovery (depth bound : Nat) :
    timePullback depth bound (nextClock depth bound - nextOne depth bound) = currentClock depth bound := by
  rw [original_time_increment, add_sub_cancel_right]
  exact SourceGeneratedRecordFrame.original_time_recovery depth bound _

theorem clock_word_transfer (depth bound : Nat) (value : FieldSpace depth bound) :
    SourceClockComplex.clock (nextWord depth bound (timeTransfer depth bound value)) =
      SourceClockComplex.clock (SourceGeneratedAcquisitionJoint.word depth bound value) +
        SourceMassCompletion.massRead (SourceGeneratedAcquisitionJoint.joint depth bound value) := by
  rw [next_word_transfer, SourceClockComplex.clock_push]
  rfl

theorem clock_word_pullback (depth bound : Nat) (value : NextSpace depth bound) :
    SourceClockComplex.clock (SourceGeneratedAcquisitionJoint.word depth bound (timePullback depth bound value)) =
      SourceClockComplex.clock (nextWord depth bound value) -
        SourceMassCompletion.massRead (nextJoint depth bound value) := by
  have actual := clock_word_transfer depth bound (timePullback depth bound value)
  rw [show timeTransfer depth bound (timePullback depth bound value) = value from
    IsometricRetainedTransfer.transfer_pullback (timePullback depth bound) value] at actual
  rw [next_joint_pullback, SourceMassCompletion.massRead_action]
  exact (eq_sub_iff_add_eq.mpr actual.symm)

end
end SourceGeneratedJointClock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
