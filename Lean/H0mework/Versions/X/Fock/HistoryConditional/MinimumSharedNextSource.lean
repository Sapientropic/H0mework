import H0mework.Versions.X.Fock.HistoryConditional.FiniteObservationMinimumCapacity
import H0mework.Versions.X.Fock.CopyGraph.SharedNextSourceStepSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceMinimumSharedNext

open SourceCopyCurrentCoordinates (maximumIndex sourceRead realize)
open SourceCopyNativeModelStep (sourceValue)
open SourceCopyTemporalBoundary (recordedPrefix)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

abbrev Window (runtime : LivingRuntimeState process) := SourceOperatorObservationAcquisition.Window runtime (maximumIndex runtime)

def native (runtime : LivingRuntimeState process) : Window runtime :=
  recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) (sourceValue runtime)

theorem next_nonunit (runtime : LivingRuntimeState process) : (maximumIndex runtime.tick.next).val ≠ 0 := by
  rw [SourceCopyCurrentCoordinates.maximum_index_val, SourceActualImageStep.next_bound]
  exact Nat.succ_ne_zero _

def step (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (previous : Window runtime) : Window runtime.tick.next :=
  recordedPrefix runtime.tick.next (maximumIndex runtime.tick.next) 0 ((maximumIndex runtime.tick.next).val + 1)
    (realize runtime.tick.next (maximumIndex runtime.tick.next) 0
      (SourceCopyNativeSharedUpdate.step runtime
        (SourceOperatorObservationAcquisition.decode runtime (maximumIndex runtime) nonunit 0 previous)))

theorem step_source (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0) :
    step runtime nonunit (native runtime) = native runtime.tick.next := by
  rw [step, native, SourceOperatorObservationAcquisition.decode_source, SourceCopyNativeSharedUpdate.step_source,
    SourceCopyNativeSharedUpdate.source_realize]
  rfl

theorem decode_step (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (previous : Window runtime) :
    SourceOperatorObservationAcquisition.decode runtime.tick.next (maximumIndex runtime.tick.next) (next_nonunit runtime) 0
      (step runtime nonunit previous) = SourceCopyNativeSharedUpdate.step runtime
        (SourceOperatorObservationAcquisition.decode runtime (maximumIndex runtime) nonunit 0 previous) := by
  rw [step, SourceOperatorObservationAcquisition.decode_source, SourceCopyCurrentCoordinates.realize_source]

theorem native_sample (runtime : LivingRuntimeState process) (phase : Fin ((maximumIndex runtime).val + 2)) :
    native runtime phase = SourceCopyTemporalBoundary.observer runtime (maximumIndex runtime) 0
      (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point (runtime.advance phase.val)))) :=
  SourceCopyTemporalBoundary.prefix_native runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1) phase

end
end SourceMinimumSharedNext
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
