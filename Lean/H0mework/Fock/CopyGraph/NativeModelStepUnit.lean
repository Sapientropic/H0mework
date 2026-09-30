import H0mework.Fock.CopyGraph.NativeModelStepGain

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeModelStep

open SourceCopyProgram (Index scale)
open SourceCopyTimeModel (time hilbert mass)
open SourceCopyFutureCoordinates (retained residual sourceRead Coordinates modelEquiv realize)
open SourceCopyTemporalBoundary (observer)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem unit_tail_source_zero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (unit : scale (inventoryBound runtime) index = 1) (target : SourceJointClockGraph.Carrier) :
    sourceRead runtime index (steps + 1) (SourceJointClockGraph.action (residual runtime index steps target)) = 0 := by
  have address := SourceCopyFutureUpdate.cutoff_step runtime index steps
  rw [unit] at address
  have mzero := congrArg (fun value : Coordinates runtime index steps => value.2.1)
    (SourceCopyFutureCoordinates.residual_source runtime index steps target)
  have czero := congrArg (fun value : Coordinates runtime index steps => value.2.2)
    (SourceCopyFutureCoordinates.residual_source runtime index steps target)
  change mass (residual runtime index steps target) = 0 at mzero
  change SourceJointClockGraph.clock (residual runtime index steps target) = 0 at czero
  apply Prod.ext
  · funext coordinate
    change hilbert (time 1 (residual runtime index steps target)) coordinate.val = 0
    have bound : coordinate.val < SourceCopyRecordedRecurrence.cutoff runtime index (steps + 2) + 1 := coordinate.isLt
    by_cases origin : coordinate.val = 0
    · exact SourceCopyTimeModel.time_hilbert_before 1 _ _ (by omega)
    · have prior : coordinate.val - 1 < SourceCopyRecordedRecurrence.cutoff runtime index (steps + 1) + 1 := by omega
      have moved := SourceCopyTimeModel.time_hilbert_add 1 (residual runtime index steps target) (coordinate.val - 1)
      rw [show coordinate.val - 1 + 1 = coordinate.val by omega] at moved
      exact moved.trans (SourceCopyFutureCoordinates.residual_inside runtime index steps target ⟨coordinate.val - 1, prior⟩)
  · apply Prod.ext
    · change mass (SourceJointClockGraph.action (residual runtime index steps target)) = 0
      rw [SourceCopyTimeModel.mass_next, mzero]
    · change SourceJointClockGraph.clock (SourceJointClockGraph.action (residual runtime index steps target)) = 0
      rw [SourceCopyTimeModel.clock_next, mzero, czero, add_zero]

theorem unit_flow_zero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (unit : scale (inventoryBound runtime) index = 1) (target : SourceJointClockGraph.Carrier) :
    flow runtime index steps target = 0 := by
  change realize runtime index (steps + 1)
    (sourceRead runtime index (steps + 1) (SourceJointClockGraph.action (residual runtime index steps target))) = 0
  rw [unit_tail_source_zero runtime index steps unit, map_zero]

def cachedAdvance (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (previous : Model SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 1))) :
    Model SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 2)) :=
  projection SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 2))
    (SourceJointClockGraph.action (realize runtime index steps (modelEquiv runtime index steps previous)))

theorem cached_advance_unit (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (unit : scale (inventoryBound runtime) index = 1) (target : SourceJointClockGraph.Carrier) :
    cachedAdvance runtime index steps
      (projection SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 1)) target) =
    projection SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 2)) (SourceJointClockGraph.action target) := by
  rw [cachedAdvance, SourceCopyFutureCoordinates.model_equiv_source]
  apply (SourceCopyFutureCoordinates.model_coordinates runtime index (steps + 1) _ _).mpr
  have source := unit_tail_source_zero runtime index steps unit target
  change sourceRead runtime index (steps + 1) (SourceJointClockGraph.action
    (target - realize runtime index steps (sourceRead runtime index steps target))) = 0 at source
  rw [map_sub, map_sub] at source
  exact (sub_eq_zero.mp source).symm

end
end SourceCopyNativeModelStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
