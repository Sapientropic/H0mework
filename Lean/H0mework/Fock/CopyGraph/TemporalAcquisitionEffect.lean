import H0mework.Fock.CopyGraph.TemporalAcquisitionRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTemporalAcquisition

open SourceCopyProgram (Index scale)
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceCopyTemporalBoundary (observer boundary newestInput)
open SourceCopyTimeModel (time)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem retained_birth_zero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (value : FieldSpace (inventoryBound runtime + steps) (inventoryBound runtime + steps)) :
    SourceRecordedEvolution.birth runtime index steps (SourceCopyGraph.action (inventoryBound runtime) index
      (fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps) value)) = 0 := by
  have actual := actual_projection_step runtime index steps (SourceCopyGraph.action (inventoryBound runtime) index
    (fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps) value))
  rw [retained_observed, observer_field_recovery] at actual
  exact add_eq_left.mp actual.symm

theorem boundary_birth (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (value : FieldSpace (inventoryBound runtime + steps) (inventoryBound runtime + steps)) :
    SourceCopyGraph.recover (inventoryBound runtime) index (SourceRecordedEvolution.birth runtime index steps
      (time (scale (inventoryBound runtime) index) (SourceCopyGraph.action (inventoryBound runtime) index
        (fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps) value)))) =
      -boundary runtime index steps (SourceCopyGraph.action (inventoryBound runtime) index
        (fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps) value)) := by
  have update := boundary_step runtime index steps (SourceCopyGraph.action (inventoryBound runtime) index
    (fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps) value))
  rw [field_boundary_closed, retained_birth_zero, map_zero, map_zero, sub_zero] at update
  apply eq_neg_iff_add_eq_zero.mpr
  with_reducible exact (add_comm _ _).trans update.symm

theorem newest_boundary_decreases (runtime : LivingRuntimeState process) (index : Index (inventoryBound (next runtime))) :
    ‖boundary (next runtime) index 1 (newestInput runtime index)‖ ^ 2 <
      ‖boundary (next runtime) index 0 (newestInput runtime index)‖ ^ 2 := by
  rw [newest_boundary_closed, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (SourceCopyTemporalBoundary.boundary_cost runtime index)

theorem newest_birth_coordinate (runtime : LivingRuntimeState process) (index : Index (inventoryBound (next runtime))) :
    SourceGeneratedBornDecoder.coordinate (inventoryBound (next runtime) + 1)
      (SourceCopyGraph.recover (inventoryBound (next runtime)) index (SourceRecordedEvolution.birth (next runtime) index 0
        (time (scale (inventoryBound (next runtime)) index) (newestInput runtime index)))) = 1 := by
  have paid : SourceCopyGraph.recover (inventoryBound (next runtime)) index (SourceRecordedEvolution.birth (next runtime) index 0
      (time (scale (inventoryBound (next runtime)) index) (newestInput runtime index))) =
        -boundary (next runtime) index 0 (newestInput runtime index) := by
    unfold newestInput
    have source := boundary_birth (next runtime) index 0
    simp only [Nat.add_zero] at source
    with_reducible exact source (SourceGeneratedBornDecoder.unitNewest runtime (inventoryBound (next runtime)))
  rw [paid, map_neg, SourceCopyTemporalBoundary.boundary_coordinate, neg_neg]

theorem newest_birth_cost (runtime : LivingRuntimeState process) (index : Index (inventoryBound (next runtime))) :
    1 ≤ ‖SourceCopyGraph.recover (inventoryBound (next runtime)) index (SourceRecordedEvolution.birth (next runtime) index 0
      (time (scale (inventoryBound (next runtime)) index) (newestInput runtime index)))‖ ^ 2 := by
  have paid : SourceCopyGraph.recover (inventoryBound (next runtime)) index (SourceRecordedEvolution.birth (next runtime) index 0
      (time (scale (inventoryBound (next runtime)) index) (newestInput runtime index))) =
        -boundary (next runtime) index 0 (newestInput runtime index) := by
    unfold newestInput
    have source := boundary_birth (next runtime) index 0
    simp only [Nat.add_zero] at source
    with_reducible exact source (SourceGeneratedBornDecoder.unitNewest runtime (inventoryBound (next runtime)))
  rw [paid, norm_neg]
  exact SourceCopyTemporalBoundary.boundary_cost runtime index

end
end SourceCopyTemporalAcquisition
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
