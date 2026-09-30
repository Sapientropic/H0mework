import H0mework.Fock.CopyGraph.LiveModelFamilyNext

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyLiveModelFamily

open SourceCopyProgram (Index)
open SourceCopyTemporalBoundary (observer)
open SourceCopyNativeModelStep (sourceValue)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceCopyCofinal.finiteComplete

theorem family_read (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    modelReadout SourceJointClockGraph.action.toLinearMap (observer runtime index 0) (family runtime index) =
      observer runtime index 0 (sourceValue runtime) := by
  rw [family_source, modelReadout_projection]

theorem family_future (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (ticks : Nat) :
    (modelAction SourceJointClockGraph.action.toLinearMap (observer runtime index 0) ^ ticks) (family runtime index) =
      projection SourceJointClockGraph.action.toLinearMap (observer runtime index 0) (sourceValue (runtime.advance ticks)) := by
  induction ticks with
  | zero =>
    rw [pow_zero, Module.End.one_apply]
    exact family_source runtime index
  | succ ticks previous =>
    rw [pow_succ']
    change modelAction SourceJointClockGraph.action.toLinearMap (observer runtime index 0)
      ((modelAction SourceJointClockGraph.action.toLinearMap (observer runtime index 0) ^ ticks) (family runtime index)) = _
    rw [previous, modelAction_source]
    exact congrArg (projection SourceJointClockGraph.action.toLinearMap (observer runtime index 0))
      (SourceCopyNativeModelStep.source_value_next (runtime.advance ticks))

theorem family_future_read (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (ticks : Nat) :
    modelReadout SourceJointClockGraph.action.toLinearMap (observer runtime index 0)
      ((modelAction SourceJointClockGraph.action.toLinearMap (observer runtime index 0) ^ ticks) (family runtime index)) =
        observer runtime index 0 (sourceValue (runtime.advance ticks)) := by
  rw [family_future, modelReadout_projection]

def prediction (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : SourceJointClockGraph.Carrier :=
  SourceCopyGraph.action (inventoryBound runtime) index
    (modelReadout SourceJointClockGraph.action.toLinearMap (observer runtime index 0) (family runtime index))

def remaining (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) : SourceJointClockGraph.Carrier :=
  sourceValue runtime - prediction runtime index

theorem original_remaining (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    remaining runtime index = SourceRecordedEvolution.residual runtime index 0 (sourceValue runtime) := by
  rw [remaining, prediction, family_read]
  rfl

theorem original_reconstruction (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    prediction runtime index + SourceRecordedEvolution.residual runtime index 0 (sourceValue runtime) = sourceValue runtime := by
  rw [← original_remaining, remaining, add_sub_cancel]

theorem family_projection (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    prediction runtime index = (SourceCopyCofinal.historyImages (inventoryBound runtime) index 0).starProjection (sourceValue runtime) := by
  rw [SourceCopyCofinal.actual_projection, prediction, family_read]
  rfl

theorem family_energy (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    ‖prediction runtime index‖ ^ 2 + ‖remaining runtime index‖ ^ 2 = ‖sourceValue runtime‖ ^ 2 := by
  rw [remaining, family_projection]
  simpa only [Submodule.starProjection_orthogonal_val] using
    (Submodule.norm_sq_eq_add_norm_sq_starProjection (sourceValue runtime)
      (SourceCopyCofinal.historyImages (inventoryBound runtime) index 0)).symm

theorem budget_material_current (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    (SourceGeneratedRuntimeMaterialStageAt.generate ((runtimeAt index.val).advance (age runtime index))).next = runtime.tick.next :=
  congrArg (fun current : LivingRuntimeState process => current.tick.next) (birth_reaches_current runtime index)

end
end SourceCopyLiveModelFamily
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
