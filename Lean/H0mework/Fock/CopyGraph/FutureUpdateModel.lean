import H0mework.Fock.CopyGraph.FutureUpdateRead

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyFutureUpdate

open SourceCopyProgram (Index scale)
open SourceCopyTemporalBoundary (observer)
open SourceCopyFutureCoordinates (modelEquiv)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def updateModel (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (previous : Model SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 1)))
    (observed : Samples runtime index) : Model SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 2)) :=
  (modelEquiv runtime index (steps + 1)).symm (update runtime index steps (modelEquiv runtime index steps previous) observed)

theorem update_model_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    updateModel runtime index steps
      (projection SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 1)) target)
      (samples runtime index steps target) = projection SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 2)) target := by
  apply (modelEquiv runtime index (steps + 1)).injective
  rw [updateModel, LinearEquiv.apply_symm_apply, SourceCopyFutureCoordinates.model_equiv_source,
    update_source, SourceCopyFutureCoordinates.model_equiv_source]

theorem dimension_gain (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    Module.finrank ℂ (Model SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 2))) =
      Module.finrank ℂ (Model SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 1))) +
        scale (inventoryBound runtime) index := by
  rw [SourceCopyFutureCoordinates.model_dimension runtime index (steps + 1),
    SourceCopyFutureCoordinates.model_dimension runtime index steps, cutoff_step]
  omega

theorem sample_count (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    Fintype.card (Fin (index.val + 1)) = scale (inventoryBound runtime) index := by
  rw [Fintype.card_fin, SourceCopyProgram.scale_source]

theorem native_query (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps ticks : Nat)
    (phase : Fin (index.val + 1)) :
    samples runtime index steps (SourceJointClockGraph.read
      (SourceClockComplex.ofNative (SourceOperationNative.point (runtime.advance ticks)))) phase =
    observer runtime index (steps + 2) (SourceJointClockGraph.read
      (SourceClockComplex.ofNative (SourceOperationNative.point (runtime.advance (ticks + phase.val))))) := by
  rw [samples, SourceCopyTemporalBoundary.prefix_source, ← SourceCopyTimeModel.time_native runtime ticks,
    SourceCopyRecordedRecurrence.time_add, SourceCopyTimeModel.time_native, Nat.add_comm phase.val ticks]

end
end SourceCopyFutureUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
