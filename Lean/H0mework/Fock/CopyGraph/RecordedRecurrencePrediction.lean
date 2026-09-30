import H0mework.Fock.CopyGraph.RecordedRecurrenceLaw

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyRecordedRecurrence

open SourceCopyProgram (Index)
open SourceCopyTimeModel (time)
open SourceCopyTemporalBoundary (observer recordedPrefix)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem window_step (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    FiniteRecurrence.advance (windowBound runtime index steps) (coefficients runtime index steps)
      (recordedPrefix runtime index steps (windowBound runtime index steps) target) =
    recordedPrefix runtime index steps (windowBound runtime index steps) (SourceJointClockGraph.action target) :=
  LinearMap.congr_fun (advance_source runtime index steps) target

theorem window_future (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps ticks : Nat)
    (target : SourceJointClockGraph.Carrier) :
    (FiniteRecurrence.advance (windowBound runtime index steps) (coefficients runtime index steps) ^ ticks)
      (recordedPrefix runtime index steps (windowBound runtime index steps) target) =
    recordedPrefix runtime index steps (windowBound runtime index steps) (time ticks target) := by
  induction ticks with
  | zero => rfl
  | succ ticks previous =>
    rw [pow_succ']
    change FiniteRecurrence.advance (windowBound runtime index steps) (coefficients runtime index steps)
      ((FiniteRecurrence.advance (windowBound runtime index steps) (coefficients runtime index steps) ^ ticks)
        (recordedPrefix runtime index steps (windowBound runtime index steps) target)) = _
    rw [previous, window_step, SourceCopyTimeModel.time_succ]

theorem read_future (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps ticks : Nat)
    (target : SourceJointClockGraph.Carrier) :
    ((FiniteRecurrence.advance (windowBound runtime index steps) (coefficients runtime index steps) ^ ticks)
      (recordedPrefix runtime index steps (windowBound runtime index steps) target)) 0 =
    observer runtime index steps (time ticks target) := by
  rw [window_future, SourceCopyTemporalBoundary.prefix_source]
  rfl

theorem native_future (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps ticks : Nat) :
    ((FiniteRecurrence.advance (windowBound runtime index steps) (coefficients runtime index steps) ^ ticks)
      (recordedPrefix runtime index steps (windowBound runtime index steps)
        (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point runtime))))) 0 =
    observer runtime index steps (SourceJointClockGraph.read
      (SourceClockComplex.ofNative (SourceOperationNative.point (runtime.advance ticks)))) := by
  rw [read_future, SourceCopyTimeModel.time_native]

theorem model_fibre (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (left right : SourceJointClockGraph.Carrier) :
    recordedPrefix runtime index steps (windowBound runtime index steps) left =
        recordedPrefix runtime index steps (windowBound runtime index steps) right ↔
      ∀ ticks : Nat, observer runtime index steps (time ticks left) = observer runtime index steps (time ticks right) := by
  rw [full_future_fibre, model_fibre_iff]
  constructor
  · intro equal ticks
    simpa only [← ContinuousLinearMap.toLinearMap_pow, ContinuousLinearMap.coe_coe, time] using equal ticks
  · intro equal ticks
    simpa only [← ContinuousLinearMap.toLinearMap_pow, ContinuousLinearMap.coe_coe, time] using equal ticks

end
end SourceCopyRecordedRecurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
