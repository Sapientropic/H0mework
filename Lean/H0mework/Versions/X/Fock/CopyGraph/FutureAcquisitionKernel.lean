import H0mework.Versions.X.Fock.CopyGraph.FutureAcquisitionRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyFutureAcquisition

open SourceCopyProgram (Index scale)
open SourceCopyTemporalBoundary (observer recordedPrefix)
open SourceCopyRecordedRecurrence (hidden windowBound)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceCopyCofinal.finiteComplete

theorem observer_kernel_decreases (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    LinearMap.ker (observer runtime index (steps + 1)) ≤ LinearMap.ker (observer runtime index steps) := by
  intro target invisible
  have newZero : (SourceCopyCofinal.historyImages (inventoryBound runtime) index (steps + 1)).starProjection target = 0 := by
    rw [SourceCopyCofinal.actual_projection, SourceCopyCofinal.advanced_action]
    change SourceCopyGraph.action (inventoryBound runtime) index (observer runtime index (steps + 1) target) = 0
    rw [show observer runtime index (steps + 1) target = 0 from invisible, map_zero]
  have source := congrArg (fun operator : SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier => operator target)
    (Submodule.starProjection_comp_starProjection_of_le
      (SourceCopyCofinal.history_images_mono (inventoryBound runtime) index (Nat.le_succ steps)))
  change (SourceCopyCofinal.historyImages (inventoryBound runtime) index steps).starProjection
    ((SourceCopyCofinal.historyImages (inventoryBound runtime) index (steps + 1)).starProjection target) =
      (SourceCopyCofinal.historyImages (inventoryBound runtime) index steps).starProjection target at source
  rw [newZero, map_zero] at source
  have actual := SourceCopyCofinal.actual_projection runtime index steps target
  rw [SourceCopyCofinal.advanced_action] at actual
  apply SourceCopyGraph.action_injective (inventoryBound runtime) index
  rw [map_zero]
  exact actual.symm.trans source.symm

theorem future_kernel_decreases (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    LinearMap.ker (sourceMap SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 1))) ≤
      LinearMap.ker (sourceMap SourceJointClockGraph.action.toLinearMap (observer runtime index steps)) := by
  intro target invisible
  apply (mem_kernel_iff _ _ target).mpr
  intro ticks
  exact observer_kernel_decreases runtime index steps ((mem_kernel_iff _ _ target).mp invisible ticks)

theorem future_kernel_strict (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    LinearMap.ker (sourceMap SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 1))) <
      LinearMap.ker (sourceMap SourceJointClockGraph.action.toLinearMap (observer runtime index steps)) := by
  apply lt_of_le_not_ge (future_kernel_decreases runtime index steps)
  intro reverse
  have old : hidden runtime index steps ∈
      LinearMap.ker (sourceMap SourceJointClockGraph.action.toLinearMap (observer runtime index steps)) := by
    apply (mem_kernel_iff _ _ _).mpr
    intro ticks
    simpa only [← ContinuousLinearMap.toLinearMap_pow, ContinuousLinearMap.coe_coe, SourceCopyTimeModel.time] using
      SourceCopyRecordedRecurrence.hidden_future_zero runtime index steps ticks
  have impossible := (mem_kernel_iff _ _ _).mp (reverse old) (scale (inventoryBound runtime) index - 1)
  apply acquired_read_nonzero runtime index steps
  simpa only [arrival, ← ContinuousLinearMap.toLinearMap_pow, ContinuousLinearMap.coe_coe, SourceCopyTimeModel.time] using impossible

theorem model_gain (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    projection SourceJointClockGraph.action.toLinearMap (observer runtime index steps) (hidden runtime index steps) =
        projection SourceJointClockGraph.action.toLinearMap (observer runtime index steps) 0 ∧
      projection SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 1)) (hidden runtime index steps) ≠
        projection SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 1)) 0 := by
  refine ⟨(SourceCopyRecordedRecurrence.full_future_fibre runtime index steps _ _).mp
    (SourceCopyRecordedRecurrence.hidden_same_window runtime index steps), ?_⟩
  intro same
  have impossible := (model_fibre_iff _ _ _ _).mp same (scale (inventoryBound runtime) index - 1)
  rw [map_zero, map_zero] at impossible
  apply acquired_read_nonzero runtime index steps
  simpa only [arrival, ← ContinuousLinearMap.toLinearMap_pow, ContinuousLinearMap.coe_coe, SourceCopyTimeModel.time] using impossible

theorem no_free_acquired_read (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    ¬ ∃ decode : PrefixCarrier SourceJointClockGraph.Carrier (windowBound runtime index steps) → SourceJointClockGraph.Carrier,
      ∀ target, decode (recordedPrefix runtime index steps (windowBound runtime index steps) target) =
        observer runtime index (steps + 1) (SourceCopyTimeModel.time (scale (inventoryBound runtime) index - 1) target) := by
  rintro ⟨decode, exactRead⟩
  have same := congrArg decode (SourceCopyRecordedRecurrence.hidden_same_window runtime index steps)
  rw [exactRead, exactRead, map_zero, map_zero] at same
  exact acquired_read_nonzero runtime index steps same

end
end SourceCopyFutureAcquisition
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
