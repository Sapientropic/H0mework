import H0mework.Versions.X.Fock.CopyGraph.TemporalBoundaryBoundary
import H0mework.Versions.X.Fock.PrimeFieldJoint.BornNormalized

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTemporalBoundary

open SourceCopyProgram (Index)
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceGeneratedActionWords.Fock.OriginalHilbert SourceSuccessorBoundary
open SourceGeneratedBornDecoder (coordinate unitNewest unitTarget)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem field_outside (depth bound : Nat) (value : FieldSpace depth bound) :
    coordinate (bound + 1) (fieldRead depth bound value) = 0 := by
  change readWord (SourceGeneratedAcquisitionJoint.word depth bound value) (bound + 1) = 0
  rw [readWord_coordinate]
  exact SourceHistoryWord.word_outside bound (Actor.currentPullback depth bound value) (bound + 1) (Nat.le_refl _)

def newestInput (runtime : LivingRuntimeState process) (index : Index (inventoryBound (next runtime))) : SourceJointClockGraph.Carrier :=
  SourceCopyGraph.action (inventoryBound (next runtime)) index
    (fieldRead (inventoryBound (next runtime)) (inventoryBound (next runtime))
      (unitNewest runtime (inventoryBound (next runtime))))

theorem newest_observed (runtime : LivingRuntimeState process) (index : Index (inventoryBound (next runtime))) :
    observer (next runtime) index 0 (newestInput runtime index) =
      fieldRead (inventoryBound (next runtime)) (inventoryBound (next runtime))
        (unitNewest runtime (inventoryBound (next runtime))) := by
  rw [observer_source, newestInput]
  exact congrArg (fieldRead (inventoryBound (next runtime)) (inventoryBound (next runtime)))
    (SourceRecordedEvolution.field_recovery (next runtime) index 0 (unitNewest runtime (inventoryBound (next runtime))))

theorem newest_time (runtime : LivingRuntimeState process) (index : Index (inventoryBound (next runtime))) :
    SourceJointClockGraph.action (observer (next runtime) index 0 (newestInput runtime index)) =
      unitTarget runtime (inventoryBound (next runtime)) := by
  rw [newest_observed]
  exact (original_time_square _ _ _).symm

theorem boundary_coordinate (runtime : LivingRuntimeState process) (index : Index (inventoryBound (next runtime))) :
    coordinate (inventoryBound (next runtime) + 1) (boundary (next runtime) index 0 (newestInput runtime index)) = -1 := by
  rw [boundary, map_sub, newest_time, SourceGeneratedBornDecoder.unit_coordinate, observer_source]
  have outside := field_outside (inventoryBound (next runtime) + 0) (inventoryBound (next runtime) + 0)
    (SourceRecordedEvolution.recovery (next runtime) index 0
      (SourceCopyTimeModel.time (SourceCopyProgram.scale (inventoryBound (next runtime)) index) (newestInput runtime index)))
  with_reducible exact (congrArg (fun value : ℂ => value - 1) outside).trans (zero_sub 1)

theorem boundary_nonzero (runtime : LivingRuntimeState process) (index : Index (inventoryBound (next runtime))) :
    boundary (next runtime) index 0 (newestInput runtime index) ≠ 0 := by
  intro zero
  have source := boundary_coordinate runtime index
  rw [zero, map_zero] at source
  norm_num at source

theorem boundary_cost (runtime : LivingRuntimeState process) (index : Index (inventoryBound (next runtime))) :
    1 ≤ ‖boundary (next runtime) index 0 (newestInput runtime index)‖ ^ 2 := by
  have price := SourceGeneratedBornDecoder.coordinate_norm_le (inventoryBound (next runtime) + 1)
    (boundary (next runtime) index 0 (newestInput runtime index))
  rw [boundary_coordinate, norm_neg, norm_one] at price
  nlinarith only [price]

theorem finite_next_missing_cost (runtime : LivingRuntimeState process) (index : Index (inventoryBound (next runtime))) :
    1 ≤ ‖(SourceCopyTimeModel.finitePhases (next runtime) index 0 (SourceJointClockGraph.action (newestInput runtime index)) -
      SourceCopyTimeModel.next (inventoryBound (next runtime)) index
        (SourceCopyTimeModel.finitePhases (next runtime) index 0 (newestInput runtime index))) (Fin.last index.val)‖ ^ 2 := by
  rw [finite_next, add_sub_cancel_left]
  simpa only [lastCell, Pi.single_eq_same] using boundary_cost runtime index

end
end SourceCopyTemporalBoundary
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
