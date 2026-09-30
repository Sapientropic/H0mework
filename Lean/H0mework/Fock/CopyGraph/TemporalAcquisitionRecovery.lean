import H0mework.Fock.CopyGraph.TemporalAcquisitionTime

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTemporalAcquisition

open SourceCopyProgram (Index scale)
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedAcquisitionJoint SourceGeneratedJointClockGraph
open SourceCopyTemporalBoundary (observer boundary)
open SourceCopyTimeModel (time)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem observer_field_recovery (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (value : FieldSpace (inventoryBound runtime + steps) (inventoryBound runtime + steps)) :
    observer runtime index steps (SourceCopyGraph.action (inventoryBound runtime) index
      (fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps) value)) =
      fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps) value := by
  rw [SourceCopyTemporalBoundary.observer_source]
  have actual := congrArg (fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps))
    (SourceRecordedEvolution.field_recovery runtime index steps value)
  simpa only [SourceCopyCofinal.advanced_action] using actual

theorem normalized_field_read (bound : Nat) (value : FieldSpace bound bound) :
    fieldRead (bound + 1) (bound + 1) (normalize bound (bound + 1) (Nat.le_succ bound) value) =
      fieldRead bound bound value := by
  change SourceJointClockGraph.read (word (bound + 1) (bound + 1) (normalize bound (bound + 1) (Nat.le_succ bound) value)) = _
  rw [normalize_word]
  rfl

theorem retained_observed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (value : FieldSpace (inventoryBound runtime + steps) (inventoryBound runtime + steps)) :
    observer runtime index (steps + 1) (SourceCopyGraph.action (inventoryBound runtime) index
      (fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps) value)) =
      fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps) value := by
  have actual := observer_field_recovery runtime index (steps + 1)
    (normalize (inventoryBound runtime + steps) ((inventoryBound runtime + steps) + 1) (Nat.le_succ _) value)
  have retained := normalized_field_read (inventoryBound runtime + steps) value
  have input := congrArg (fun source => observer runtime index (steps + 1)
    (SourceCopyGraph.action (inventoryBound runtime) index source)) retained
  with_reducible exact input.symm.trans (actual.trans retained)

theorem future_observed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (value : FieldSpace (inventoryBound runtime + steps) (inventoryBound runtime + steps)) :
    observer runtime index (steps + 1) (time (scale (inventoryBound runtime) index)
      (SourceCopyGraph.action (inventoryBound runtime) index
        (fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps) value))) =
      SourceJointClockGraph.action (fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps) value) := by
  rw [copy_time_field]
  have actual := observer_field_recovery runtime index (steps + 1)
    (timeField (inventoryBound runtime + steps) (inventoryBound runtime + steps) value)
  exact actual.trans (time_field_read _ _ value)

theorem field_boundary_closed (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (value : FieldSpace (inventoryBound runtime + steps) (inventoryBound runtime + steps)) :
    boundary runtime index (steps + 1) (SourceCopyGraph.action (inventoryBound runtime) index
      (fieldRead (inventoryBound runtime + steps) (inventoryBound runtime + steps) value)) = 0 := by
  rw [boundary, future_observed, retained_observed, sub_self]

theorem newest_boundary_closed (runtime : LivingRuntimeState process) (index : Index (inventoryBound (next runtime))) :
    boundary (next runtime) index 1 (SourceCopyTemporalBoundary.newestInput runtime index) = 0 :=
  field_boundary_closed (next runtime) index 0 (SourceGeneratedBornDecoder.unitNewest runtime (inventoryBound (next runtime)))

end
end SourceCopyTemporalAcquisition
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
