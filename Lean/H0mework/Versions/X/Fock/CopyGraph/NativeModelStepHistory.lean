import H0mework.Versions.X.Fock.CopyGraph.NativeModelStepNonunit

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeModelStep

open SourceCopyProgram (Index)
open SourceCopyTemporalBoundary (observer recordedPrefix)
open SourceCopyFutureCoordinates (modelEquiv decode)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def sourceValue (runtime : LivingRuntimeState process) : SourceJointClockGraph.Carrier :=
  SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point runtime))

theorem source_value_next (runtime : LivingRuntimeState process) :
    SourceJointClockGraph.action (sourceValue runtime) = sourceValue runtime.tick.next :=
  SourceJointClockGraph.native_next runtime

def cache (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    (stage : Nat) → Model SourceJointClockGraph.action.toLinearMap (observer runtime index (stage + 1))
  | 0 => (modelEquiv runtime index 0).symm (decode runtime index 0
      (recordedPrefix runtime index 1 (SourceCopyRecordedRecurrence.windowBound runtime index 1) (sourceValue runtime.tick.next)))
  | stage + 1 => advanceModel runtime index stage (cache runtime index stage)
      (SourceCopyFutureUpdate.samples runtime index stage (sourceValue (runtime.advance (stage + 1))))

theorem cache_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (stage : Nat) :
    cache runtime index stage = projection SourceJointClockGraph.action.toLinearMap (observer runtime index (stage + 1))
      (sourceValue (runtime.advance (stage + 1))) := by
  induction stage with
  | zero =>
      apply (modelEquiv runtime index 0).injective
      rw [cache, LinearEquiv.apply_symm_apply, SourceCopyFutureCoordinates.decode_source,
        SourceCopyFutureCoordinates.model_equiv_source]
      rfl
  | succ stage previous =>
      rw [cache, previous]
      exact native_model_next runtime index stage (stage + 1)

theorem cache_at_material (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (stage : Nat)
    (material : SourceGeneratedRuntimeMaterialStageAt (runtime.advance stage)) :
    cache runtime index stage = projection SourceJointClockGraph.action.toLinearMap (observer runtime index (stage + 1))
      (sourceValue material.next) := by
  exact cache_source runtime index stage

theorem cache_gain_budget (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (stage : Nat)
    (material : SourceGeneratedRuntimeMaterialStageAt (runtime.advance (stage + 1))) :
    ‖advanceGain runtime index stage (cache runtime index stage)
      (SourceCopyFutureUpdate.samples runtime index stage (sourceValue (runtime.advance (stage + 1))))‖ ^ 2 +
      ‖SourceCopyFutureCoordinates.residual runtime index (stage + 1) (sourceValue material.next)‖ ^ 2 =
        ‖SourceCopyFutureCoordinates.residual runtime index stage (sourceValue (runtime.advance (stage + 1)))‖ ^ 2 := by
  rw [cache_source]
  have actual := advance_gain_budget runtime index stage (sourceValue (runtime.advance (stage + 1)))
  rw [source_value_next] at actual
  exact actual

end
end SourceCopyNativeModelStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
