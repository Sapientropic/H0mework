import H0mework.Versions.X.Fock.CopyGraph.CurrentCoordinatesShared
import H0mework.Versions.X.Fock.CopyGraph.SharedNextFlow

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopySharedNext

open SourceCopyCurrentCoordinates (maximumIndex sourceRead Coordinates realize shared jointObserver jointModelEquiv)
open SourceCopyTimeModel (finitePhases)
open SourceCopyNativeModelStep (sourceValue)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def updateModel (runtime : LivingRuntimeState process)
    (previous : Model SourceJointClockGraph.action.toLinearMap (jointObserver runtime)) (packet : NextPacket runtime) :
    Model SourceJointClockGraph.action.toLinearMap (jointObserver runtime.tick.next) :=
  (jointModelEquiv runtime.tick.next).symm (update runtime (jointModelEquiv runtime previous) packet)

theorem update_model_source (runtime : LivingRuntimeState process) (target : SourceJointClockGraph.Carrier) :
    updateModel runtime (projection SourceJointClockGraph.action.toLinearMap (jointObserver runtime) target)
      (finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target)) =
        projection SourceJointClockGraph.action.toLinearMap (jointObserver runtime.tick.next) (SourceJointClockGraph.action target) := by
  rw [updateModel, SourceCopyCurrentCoordinates.joint_model_source, update_source,
    ← SourceCopyCurrentCoordinates.joint_model_source runtime.tick.next (SourceJointClockGraph.action target), LinearEquiv.symm_apply_apply]

def gain (runtime : LivingRuntimeState process) (previous : Coordinates runtime (maximumIndex runtime) 0) (packet : NextPacket runtime) :
    SourceJointClockGraph.Carrier :=
  realize runtime.tick.next (maximumIndex runtime.tick.next) 0 (update runtime previous packet) -
    SourceJointClockGraph.action (realize runtime (maximumIndex runtime) 0 previous)

theorem gain_source (runtime : LivingRuntimeState process) (target : SourceJointClockGraph.Carrier) :
    gain runtime (sourceRead runtime (maximumIndex runtime) 0 target)
      (finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target)) = flow runtime target := by
  rw [gain, update_source]
  change SourceCopyCurrentCoordinates.retained runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target) -
    SourceJointClockGraph.action (SourceCopyCurrentCoordinates.retained runtime (maximumIndex runtime) 0 target) = _
  rw [next_reconstruction, add_sub_cancel_left]

theorem gain_budget (runtime : LivingRuntimeState process) (target : SourceJointClockGraph.Carrier) :
    ‖gain runtime (sourceRead runtime (maximumIndex runtime) 0 target)
      (finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target))‖ ^ 2 +
      ‖SourceCopyCurrentCoordinates.residual runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target)‖ ^ 2 =
        ‖SourceCopyCurrentCoordinates.residual runtime (maximumIndex runtime) 0 target‖ ^ 2 := by
  rw [gain_source]
  exact flow_budget runtime target

theorem native_budget (runtime : LivingRuntimeState process) :
    ‖gain runtime (shared runtime) (finitePhases runtime.tick.next (maximumIndex runtime.tick.next) 0 (sourceValue runtime.tick.next))‖ ^ 2 +
      ‖SourceCopyCurrentCoordinates.residual runtime.tick.next (maximumIndex runtime.tick.next) 0 (sourceValue runtime.tick.next)‖ ^ 2 =
        ‖SourceCopyCurrentCoordinates.residual runtime (maximumIndex runtime) 0 (sourceValue runtime)‖ ^ 2 := by
  have source := gain_budget runtime (sourceValue runtime)
  rw [SourceCopyNativeModelStep.source_value_next] at source
  simpa only [SourceCopyCurrentCoordinates.shared_source] using source

end
end SourceCopySharedNext
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
