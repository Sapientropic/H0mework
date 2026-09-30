import H0mework.Versions.X.Fock.CopyGraph.FutureAcquisitionKernel

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyFutureAcquisition

open SourceCopyProgram (Index)
open SourceCopyTemporalBoundary (observer)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem old_residual (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    SourceRecordedEvolution.residual runtime index steps (arrival runtime index steps) = arrival runtime index steps := by
  rw [SourceRecordedEvolution.residual, SourceCopyCofinal.advanced_action]
  change arrival runtime index steps - SourceCopyGraph.action (inventoryBound runtime) index
    (observer runtime index steps (arrival runtime index steps)) = _
  rw [old_read_zero, map_zero, sub_zero]

theorem acquired_energy (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    ‖SourceRecordedEvolution.residual runtime index (steps + 1) (arrival runtime index steps)‖ ^ 2 +
      ‖SourceRecordedEvolution.birth runtime index steps (arrival runtime index steps)‖ ^ 2 =
        ‖arrival runtime index steps‖ ^ 2 := by
  have source := SourceCompleteGraph.energy_step 0 runtime index steps (arrival runtime index steps)
  rw [← SourceRecordedEvolution.residual_original 0, ← SourceRecordedEvolution.birth_original 0,
    ← SourceRecordedEvolution.residual_original 0, old_residual] at source
  exact source

theorem acquired_error_strict (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    ‖SourceRecordedEvolution.residual runtime index (steps + 1) (arrival runtime index steps)‖ ^ 2 <
      ‖SourceRecordedEvolution.residual runtime index steps (arrival runtime index steps)‖ ^ 2 := by
  rw [old_residual]
  have positive : 0 < ‖SourceRecordedEvolution.birth runtime index steps (arrival runtime index steps)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (birth_nonzero runtime index steps))
  linarith only [acquired_energy runtime index steps, positive]

theorem recovered_birth_budget (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    ‖SourceCopyGraph.action (inventoryBound runtime) index
      (observer runtime index (steps + 1) (arrival runtime index steps))‖ ^ 2 +
        ‖SourceRecordedEvolution.residual runtime index (steps + 1) (arrival runtime index steps)‖ ^ 2 =
          ‖arrival runtime index steps‖ ^ 2 := by
  have actual := SourceCopyTemporalAcquisition.actual_projection_step runtime index steps (arrival runtime index steps)
  rw [old_read_zero, map_zero, zero_add] at actual
  rw [actual, add_comm]
  exact acquired_energy runtime index steps

end
end SourceCopyFutureAcquisition
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
