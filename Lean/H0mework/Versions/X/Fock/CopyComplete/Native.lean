import H0mework.Versions.X.Fock.CopyComplete.History
import H0mework.Versions.X.Fock.CopyComplete.Boundary

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCompleteGraph

open SourceGeneratedAcquisitionMeasure SourceGeneratedAcquisitionJoint SourceGeneratedAcquisitionContinuation SourceGeneratedJointClockGraph
open SourceGeneratedActionWords.Fock SourceGeneratedActionWords.Fock.Dynamic
open SourceGeneratedActionWords.Fock.OriginalHilbert
open SourceOwnedObservationHistory
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] completeUniform completeMeasurable completeBorel completeT2

theorem retained_source_recovery (model depth : Nat) (index : Index depth) (value : FieldSpace depth depth) :
    SourceConditionalGraphDecoder.residual (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index)
      (Hilbert.read model (depth + 1)) (SourceCopyGraph.action depth index (fieldRead depth depth value)) = 0 := by
  have exactSource := source_recovery model (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index)
    (Actor.currentPullback (depth + 1) (depth + 1) (normalize depth (depth + 1) (Nat.le_succ depth) value))
  change SourceConditionalGraphDecoder.residual (depth + 1) (depth + 1) (FamilyModel.Fock.oldIndex depth index)
    (Hilbert.read model (depth + 1))
    (SourceCopyGraph.action (depth + 1) (FamilyModel.Fock.oldIndex depth index)
      (fieldRead (depth + 1) (depth + 1) (normalize depth (depth + 1) (Nat.le_succ depth) value))) = 0 at exactSource
  rw [SourceGraphGrowth.field_retained_target] at exactSource
  exact exactSource

theorem old_pulse_preserved (model : Nat) (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) :
    residual model runtime index 1 (SourceGraphGrowth.pulse (inventoryBound runtime) index) = 0 := by
  rw [residual_canonical]
  have actual := retained_source_recovery model (inventoryBound runtime) index (SourceGraphGrowth.pulseField (inventoryBound runtime) index)
  rw [SourceGraphGrowth.pulse_field_read] at actual
  exact actual

theorem native_complete_recovery :
    residual 2 (runtimeAt 2) (0 : Index (inventoryBound (runtimeAt 2))) 1
      (SourceGraphGrowth.pulse (inventoryBound (runtimeAt 2)) (0 : Index (inventoryBound (runtimeAt 2)))) = 0 :=
  old_pulse_preserved 2 (runtimeAt 2) 0

theorem history_boundary_nonzero (model : Nat) (runtime : LivingRuntimeState process)
    (index : Index (inventoryBound runtime)) (steps : Nat) : residual model runtime index steps boundary ≠ 0 := by
  rw [residual_canonical]
  exact boundary_residual_nonzero model _ _ _

end
end SourceCompleteGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
