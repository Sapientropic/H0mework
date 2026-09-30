import H0mework.Fock.CopyGraph.FutureUpdateAccount

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyFutureUpdate

open SourceCopyProgram (Index)
open SourceCopyFutureCoordinates (retained residual sourceRead)
open SourceCopyTemporalBoundary (observer)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem no_free_update (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    ¬ ∃ restore : Model SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 1)) →
        Model SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 2)),
      ∀ target : SourceJointClockGraph.Carrier,
        restore (projection SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 1)) target) =
          projection SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 2)) target := by
  rintro ⟨restore, exactSource⟩
  have source := SourceCopyFutureAcquisition.model_gain runtime index (steps + 1)
  have same := congrArg restore source.1
  rw [exactSource, exactSource] at same
  exact source.2 same

theorem block_nonzero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    block runtime index steps (SourceCopyRecordedRecurrence.hidden runtime index (steps + 1)) ≠ 0 := by
  intro vanished
  have kept := retained_step runtime index steps (SourceCopyRecordedRecurrence.hidden runtime index (steps + 1))
  rw [SourceCopyFutureCoordinates.hidden_retained, vanished, zero_add] at kept
  have same := congrArg (sourceRead runtime index (steps + 1)) kept
  change sourceRead runtime index (steps + 1) (SourceCopyFutureCoordinates.realize runtime index (steps + 1)
    (sourceRead runtime index (steps + 1) (SourceCopyRecordedRecurrence.hidden runtime index (steps + 1)))) =
      sourceRead runtime index (steps + 1) 0 at same
  rw [SourceCopyFutureCoordinates.realize_source] at same
  exact (SourceCopyFutureAcquisition.model_gain runtime index (steps + 1)).2
    ((SourceCopyFutureCoordinates.model_coordinates runtime index (steps + 1) _ _).mpr same)

theorem tail_strict (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    ‖residual runtime index (steps + 1) (SourceCopyRecordedRecurrence.hidden runtime index (steps + 1))‖ ^ 2 <
      ‖residual runtime index steps (SourceCopyRecordedRecurrence.hidden runtime index (steps + 1))‖ ^ 2 := by
  have positive := sq_pos_of_pos (norm_pos_iff.mpr (block_nonzero runtime index steps))
  linarith only [positive, block_budget runtime index steps (SourceCopyRecordedRecurrence.hidden runtime index (steps + 1))]

end
end SourceCopyFutureUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
