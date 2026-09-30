import H0mework.Versions.X.Fock.CopyGraph.TemporalBoundaryObservation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTemporalAcquisition

open SourceCopyProgram (Index)
open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionContinuation SourceGeneratedAcquisitionJoint SourceGeneratedJointClockGraph
open SourceOwnedObservationHistory
open SourceCopyTemporalBoundary (observer boundary)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem direction_source (depth : Nat) (index : Index depth)
    (previous : SourceJointClockGraph.Carrier → FieldSpace depth depth) :
    SourceCopyGraph.action (depth + 1) (FamilyModel.Fock.oldIndex depth index)
      (fieldRead (depth + 1) (depth + 1) (SourceRecordedEvolution.direction depth index previous)) =
      SourceRecordedEvolution.innovation depth index previous := by
  rw [SourceRecordedEvolution.direction, map_sub, map_sub, SourceGraphBirth.fresh_field_source,
    SourceGraphGrowth.field_retained_target]
  rfl

theorem step_source (depth : Nat) (index : Index depth)
    (previous : SourceJointClockGraph.Carrier → FieldSpace depth depth) (target : SourceJointClockGraph.Carrier) :
    SourceCopyGraph.action (depth + 1) (FamilyModel.Fock.oldIndex depth index)
      (fieldRead (depth + 1) (depth + 1) (SourceRecordedEvolution.step depth index previous target)) =
    SourceCopyGraph.action depth index (fieldRead depth depth (previous target)) +
      (inner ℂ (SourceRecordedEvolution.innovation depth index previous) target /
        ((‖SourceRecordedEvolution.innovation depth index previous‖ ^ 2 : ℝ) : ℂ)) •
      SourceRecordedEvolution.innovation depth index previous := by
  rw [SourceRecordedEvolution.step, map_add, map_add, map_smul, map_smul,
    SourceGraphGrowth.field_retained_target, direction_source]

theorem actual_projection_step (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    SourceCopyGraph.action (inventoryBound runtime) index (observer runtime index (steps + 1) target) =
      SourceCopyGraph.action (inventoryBound runtime) index (observer runtime index steps target) +
        SourceRecordedEvolution.birth runtime index steps target := by
  rw [SourceCopyTemporalBoundary.observer_source, SourceCopyTemporalBoundary.observer_source]
  conv_lhs => rw [← SourceCopyCofinal.advanced_action (inventoryBound runtime) index (steps + 1)]
  conv_rhs => rw [← SourceCopyCofinal.advanced_action (inventoryBound runtime) index steps]
  change SourceCopyGraph.action ((inventoryBound runtime + steps) + 1)
    (FamilyModel.Fock.oldIndex (inventoryBound runtime + steps) (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps))
    (fieldRead ((inventoryBound runtime + steps) + 1) ((inventoryBound runtime + steps) + 1)
      (SourceRecordedEvolution.step (inventoryBound runtime + steps) (SourceGraphLoss.advancedIndex (inventoryBound runtime) index steps)
        (SourceRecordedEvolution.recovery runtime index steps) target)) = _
  exact step_source _ _ _ target

theorem observer_step (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    observer runtime index (steps + 1) target = observer runtime index steps target +
      SourceCopyGraph.recover (inventoryBound runtime) index (SourceRecordedEvolution.birth runtime index steps target) := by
  have source := congrArg (SourceCopyGraph.recover (inventoryBound runtime) index) (actual_projection_step runtime index steps target)
  simpa only [map_add, SourceCopyGraph.recover_action] using source

theorem boundary_step (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (steps : Nat) (target : SourceJointClockGraph.Carrier) :
    boundary runtime index (steps + 1) target = boundary runtime index steps target +
      SourceCopyGraph.recover (inventoryBound runtime) index (SourceRecordedEvolution.birth runtime index steps
        (SourceCopyTimeModel.time (SourceCopyProgram.scale (inventoryBound runtime) index) target)) -
      SourceJointClockGraph.action (SourceCopyGraph.recover (inventoryBound runtime) index
        (SourceRecordedEvolution.birth runtime index steps target)) := by
  rw [boundary, boundary, observer_step, observer_step, map_add]
  abel

end
end SourceCopyTemporalAcquisition
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
