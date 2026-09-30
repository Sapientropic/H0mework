import H0mework.Fock.CopyGraph.NativeModelStepUnit

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeModelStep

open SourceCopyProgram (Index scale)
open SourceCopyTimeModel (time hilbert)
open SourceCopyRecordedRecurrence (cutoff hidden)
open SourceCopyFutureCoordinates (sourceRead Coordinates residual)
open SourceCopyTemporalBoundary (observer)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem shifted_hidden_coordinate (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    hilbert (SourceJointClockGraph.action (hidden runtime index (steps + 1))) (cutoff runtime index (steps + 1) + 2) = 1 := by
  have shifted := SourceCopyTimeModel.time_hilbert_add 1 (hidden runtime index (steps + 1)) (cutoff runtime index (steps + 1) + 1)
  rw [SourceCopyRecordedRecurrence.hidden_coordinate] at shifted
  exact shifted

def recoveredCoordinate (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (nonunit : index.val ≠ 0) : Fin (cutoff runtime index (steps + 2) + 1) :=
  ⟨cutoff runtime index (steps + 1) + 2, by
    have address := SourceCopyFutureUpdate.cutoff_step runtime index steps
    have count := SourceCopyProgram.scale_source (inventoryBound runtime) index
    omega⟩

theorem flow_hidden_coordinate (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (nonunit : index.val ≠ 0) :
    hilbert (flow runtime index steps (hidden runtime index (steps + 1))) (cutoff runtime index (steps + 1) + 2) = 1 := by
  have realized := SourceCopyFutureCoordinates.realize_source runtime index (steps + 1)
    (sourceRead runtime index (steps + 1) (SourceJointClockGraph.action (residual runtime index steps (hidden runtime index (steps + 1)))))
  have source := congrArg (fun value : Coordinates runtime index (steps + 1) => value.1 (recoveredCoordinate runtime index steps nonunit)) realized
  change hilbert (flow runtime index steps (hidden runtime index (steps + 1))) (cutoff runtime index (steps + 1) + 2) =
    hilbert (SourceJointClockGraph.action (residual runtime index steps (hidden runtime index (steps + 1))))
      (cutoff runtime index (steps + 1) + 2) at source
  rw [SourceCopyFutureCoordinates.hidden_residual, shifted_hidden_coordinate] at source
  exact source

theorem flow_nonzero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (nonunit : index.val ≠ 0) : flow runtime index steps (hidden runtime index (steps + 1)) ≠ 0 := by
  intro vanished
  have source := flow_hidden_coordinate runtime index steps nonunit
  rw [vanished] at source
  change (0 : ℂ) = 1 at source
  exact zero_ne_one source

theorem no_cached_nonunit (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (nonunit : index.val ≠ 0) :
    ¬ ∃ restore : Model SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 1)) →
        Model SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 2)),
      ∀ target : SourceJointClockGraph.Carrier,
        restore (projection SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 1)) target) =
          projection SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 2)) (SourceJointClockGraph.action target) := by
  rintro ⟨restore, exactSource⟩
  have same := congrArg restore (SourceCopyFutureAcquisition.model_gain runtime index (steps + 1)).1
  rw [exactSource, exactSource, map_zero] at same
  have coordinates := (SourceCopyFutureCoordinates.model_coordinates runtime index (steps + 1) _ _).mp same
  have read := congrArg (fun value : Coordinates runtime index (steps + 1) => value.1 (recoveredCoordinate runtime index steps nonunit)) coordinates
  change hilbert (SourceJointClockGraph.action (hidden runtime index (steps + 1))) (cutoff runtime index (steps + 1) + 2) = 0 at read
  rw [shifted_hidden_coordinate] at read
  exact one_ne_zero read

theorem nonunit_tail_decreases (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (nonunit : index.val ≠ 0) :
    ‖residual runtime index (steps + 1) (SourceJointClockGraph.action (hidden runtime index (steps + 1)))‖ ^ 2 <
      ‖residual runtime index steps (hidden runtime index (steps + 1))‖ ^ 2 := by
  have positive := sq_pos_of_pos (norm_pos_iff.mpr (flow_nonzero runtime index steps nonunit))
  linarith only [positive, flow_budget runtime index steps (hidden runtime index (steps + 1))]

end
end SourceCopyNativeModelStep
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
