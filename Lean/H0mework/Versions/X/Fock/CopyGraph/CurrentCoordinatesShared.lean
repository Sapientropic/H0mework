import H0mework.Versions.X.Fock.CopyGraph.CurrentCoordinatesJoint
import H0mework.Versions.X.Fock.CopyGraph.SharedHistoryEvolution
import H0mework.Versions.X.Fock.CopyGraph.LiveModelFamilyAccount

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyCurrentCoordinates

open SourceCopyProgram (Index)
open SourceCopyTemporalBoundary (observer)
open SourceCopyNativeModelStep (sourceValue)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def shared (runtime : LivingRuntimeState process) : Coordinates runtime (maximumIndex runtime) 0 :=
  SourceCopySharedHistory.canonical runtime

theorem shared_source (runtime : LivingRuntimeState process) :
    shared runtime = sourceRead runtime (maximumIndex runtime) 0 (sourceValue runtime) :=
  SourceCopySharedHistory.canonical_source runtime

def expand (runtime : LivingRuntimeState process) (value : Coordinates runtime (maximumIndex runtime) 0)
    (index : Index (inventoryBound runtime)) : Model SourceJointClockGraph.action.toLinearMap (observer runtime index 0) :=
  (modelEquiv runtime index 0).symm (restrictCoordinates runtime index value)

theorem expand_source (runtime : LivingRuntimeState process) (target : SourceJointClockGraph.Carrier)
    (index : Index (inventoryBound runtime)) :
    expand runtime (sourceRead runtime (maximumIndex runtime) 0 target) index =
      projection SourceJointClockGraph.action.toLinearMap (observer runtime index 0) target := by
  rw [expand, restrict_source, ← model_equiv_source runtime index 0 target, LinearEquiv.symm_apply_apply]

theorem shared_family (runtime : LivingRuntimeState process) : expand runtime (shared runtime) = SourceCopyLiveModelFamily.family runtime := by
  funext index
  rw [shared_source, expand_source, SourceCopyLiveModelFamily.family_source]

theorem shared_next (runtime : LivingRuntimeState process) :
    SourceCopyLiveModelFamily.next runtime (expand runtime (shared runtime)) = SourceCopyLiveModelFamily.family runtime.tick.next := by
  rw [shared_family, SourceCopyLiveModelFamily.family_next]

theorem shared_original_read (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (ticks : Nat) :
    modelReadout SourceJointClockGraph.action.toLinearMap (observer runtime index 0)
      ((modelAction SourceJointClockGraph.action.toLinearMap (observer runtime index 0) ^ ticks)
        (expand runtime (shared runtime) index)) = observer runtime index 0 (sourceValue (runtime.advance ticks)) := by
  rw [shared_family]
  exact SourceCopyLiveModelFamily.family_future_read runtime index ticks

theorem shared_reconstruction (runtime : LivingRuntimeState process) :
    realize runtime (maximumIndex runtime) 0 (shared runtime) + residual runtime (maximumIndex runtime) 0 (sourceValue runtime) = sourceValue runtime := by
  rw [shared_source]
  exact reconstruction runtime (maximumIndex runtime) 0 (sourceValue runtime)

theorem shared_energy (runtime : LivingRuntimeState process) :
    ‖realize runtime (maximumIndex runtime) 0 (shared runtime)‖ ^ 2 + ‖residual runtime (maximumIndex runtime) 0 (sourceValue runtime)‖ ^ 2 =
      ‖sourceValue runtime‖ ^ 2 := by
  rw [shared_source]
  have paid := window_energy runtime (maximumIndex runtime) 0 (sourceValue runtime)
  rwa [decode_source] at paid

end
end SourceCopyCurrentCoordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
