import H0mework.Versions.X.Fock.CopyGraph.SharedNextSourceStepProjection
import H0mework.Versions.X.Fock.CopyGraph.SharedNextPhaseSupport

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeSharedUpdate

open SourceCopyCurrentCoordinates (maximumIndex sourceRead realize)
open SourceCopyNativeModelStep (sourceValue)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem source_realize (runtime : LivingRuntimeState process) :
    realize runtime (maximumIndex runtime) 0 (sourceRead runtime (maximumIndex runtime) 0 (sourceValue runtime)) = sourceValue runtime := by
  have source := SourceCopyCurrentCoordinates.reconstruction runtime (maximumIndex runtime) 0 (sourceValue runtime)
  rw [SourceCopyPhaseRecovery.native_tail_zero, add_zero] at source
  exact source

theorem trajectory_source (runtime : LivingRuntimeState process) (stage : Nat) :
    trajectory runtime (sourceRead runtime (maximumIndex runtime) 0 (sourceValue runtime)) stage =
      sourceRead (runtime.advance stage) (maximumIndex (runtime.advance stage)) 0 (sourceValue (runtime.advance stage)) := by
  rw [trajectory, source_realize]
  have source := SourceCopyTimeModel.time_native runtime stage
  change SourceCopyTimeModel.time stage (sourceValue runtime) = sourceValue (runtime.advance stage) at source
  rw [source]

theorem step_source (runtime : LivingRuntimeState process) :
    step runtime (sourceRead runtime (maximumIndex runtime) 0 (sourceValue runtime)) =
      sourceRead runtime.tick.next (maximumIndex runtime.tick.next) 0 (sourceValue runtime.tick.next) := by
  rw [step, source_realize, SourceCopyNativeModelStep.source_value_next]

end
end SourceCopyNativeSharedUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
