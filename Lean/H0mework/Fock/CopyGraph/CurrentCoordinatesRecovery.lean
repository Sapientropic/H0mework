import H0mework.Fock.CopyGraph.CurrentCoordinatesDimension

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyCurrentCoordinates

open SourceCopyProgram (Index)
open SourceCopyRecordedRecurrence (windowBound hidden)
open SourceCopyTemporalBoundary (recordedPrefix)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem window_reconstruction (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    realize runtime index steps (decode runtime index steps
      (recordedPrefix runtime index steps (windowBound runtime index steps) target)) +
        residual runtime index steps target = target := by
  rw [window_recovery, reconstruction]

theorem window_energy (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    ‖realize runtime index steps (decode runtime index steps
      (recordedPrefix runtime index steps (windowBound runtime index steps) target))‖ ^ 2 +
        ‖residual runtime index steps target‖ ^ 2 = ‖target‖ ^ 2 := by
  rw [window_recovery, energy]

theorem hidden_retained (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    retained runtime index steps (hidden runtime index steps) = 0 := by
  have same := congrArg (decode runtime index steps) (SourceCopyRecordedRecurrence.hidden_same_window runtime index steps)
  rw [decode_source, decode_source, map_zero] at same
  rw [retained, LinearMap.comp_apply, same, map_zero]

theorem hidden_residual (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    residual runtime index steps (hidden runtime index steps) = hidden runtime index steps := by
  rw [residual, LinearMap.sub_apply, LinearMap.id_apply, hidden_retained, sub_zero]

end
end SourceCopyCurrentCoordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
