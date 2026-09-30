import H0mework.Fock.CopyGraph.SharedNextGain

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopySharedNext

open SourceCopyCurrentCoordinates (maximumIndex sourceRead Coordinates)
open SourceCopyRecordedRecurrence (cutoff hidden)
open SourceCopyTimeModel (hilbert time)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def freshCoordinate (runtime : LivingRuntimeState process) : Fin (cutoff runtime.tick.next (maximumIndex runtime.tick.next) 0 + 1) :=
  ⟨cutoff runtime (maximumIndex runtime) 0 + 2, by have growth := cutoff_growth runtime; omega⟩

theorem hidden_source_zero (runtime : LivingRuntimeState process) :
    sourceRead runtime (maximumIndex runtime) 0 (hidden runtime (maximumIndex runtime) 0) = 0 := by
  have source := SourceCopyCurrentCoordinates.residual_source runtime (maximumIndex runtime) 0 (hidden runtime (maximumIndex runtime) 0)
  rwa [SourceCopyCurrentCoordinates.hidden_residual] at source

theorem shifted_hidden_coordinate (runtime : LivingRuntimeState process) :
    (sourceRead runtime.tick.next (maximumIndex runtime.tick.next) 0
      (SourceJointClockGraph.action (hidden runtime (maximumIndex runtime) 0))).1 (freshCoordinate runtime) = 1 := by
  have moved := SourceCopyTimeModel.time_hilbert_add 1 (hidden runtime (maximumIndex runtime) 0)
    (cutoff runtime (maximumIndex runtime) 0 + 1)
  exact moved.trans (SourceCopyRecordedRecurrence.hidden_coordinate runtime (maximumIndex runtime) 0)

theorem no_free_update (runtime : LivingRuntimeState process) :
    ¬ ∃ next : Coordinates runtime (maximumIndex runtime) 0 → Coordinates runtime.tick.next (maximumIndex runtime.tick.next) 0,
      ∀ target : SourceJointClockGraph.Carrier,
        next (sourceRead runtime (maximumIndex runtime) 0 target) =
          sourceRead runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action target) := by
  rintro ⟨next, generates⟩
  have same := congrArg next ((hidden_source_zero runtime).trans
    (map_zero (sourceRead runtime (maximumIndex runtime) 0)).symm)
  rw [generates, generates, map_zero, map_zero] at same
  have impossible := congrArg (fun value : Coordinates runtime.tick.next (maximumIndex runtime.tick.next) 0 =>
    value.1 (freshCoordinate runtime)) same
  rw [shifted_hidden_coordinate] at impossible
  exact one_ne_zero impossible

theorem flow_nonzero (runtime : LivingRuntimeState process) : flow runtime (hidden runtime (maximumIndex runtime) 0) ≠ 0 := by
  intro vanished
  have source : sourceRead runtime.tick.next (maximumIndex runtime.tick.next) 0 (flow runtime (hidden runtime (maximumIndex runtime) 0)) =
      sourceRead runtime.tick.next (maximumIndex runtime.tick.next) 0 (SourceJointClockGraph.action (hidden runtime (maximumIndex runtime) 0)) := by
    change sourceRead runtime.tick.next (maximumIndex runtime.tick.next) 0
      (SourceCopyCurrentCoordinates.realize runtime.tick.next (maximumIndex runtime.tick.next) 0
        (sourceRead runtime.tick.next (maximumIndex runtime.tick.next) 0
          (SourceJointClockGraph.action (SourceCopyCurrentCoordinates.residual runtime (maximumIndex runtime) 0 (hidden runtime (maximumIndex runtime) 0))))) = _
    rw [SourceCopyCurrentCoordinates.realize_source, SourceCopyCurrentCoordinates.hidden_residual]
  rw [vanished, map_zero] at source
  have impossible := congrArg (fun value : Coordinates runtime.tick.next (maximumIndex runtime.tick.next) 0 =>
    value.1 (freshCoordinate runtime)) source
  rw [shifted_hidden_coordinate] at impossible
  exact zero_ne_one impossible

theorem hidden_tail_decreases (runtime : LivingRuntimeState process) :
    ‖SourceCopyCurrentCoordinates.residual runtime.tick.next (maximumIndex runtime.tick.next) 0
      (SourceJointClockGraph.action (hidden runtime (maximumIndex runtime) 0))‖ ^ 2 <
        ‖SourceCopyCurrentCoordinates.residual runtime (maximumIndex runtime) 0 (hidden runtime (maximumIndex runtime) 0)‖ ^ 2 := by
  have positive := sq_pos_of_pos (norm_pos_iff.mpr (flow_nonzero runtime))
  have balance := flow_budget runtime (hidden runtime (maximumIndex runtime) 0)
  linarith only [positive, balance]

end
end SourceCopySharedNext
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
