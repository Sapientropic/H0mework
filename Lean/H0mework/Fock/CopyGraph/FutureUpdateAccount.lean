import H0mework.Fock.CopyGraph.FutureUpdateBlock

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyFutureUpdate

open SourceCopyProgram (Index)
open SourceCopyFutureCoordinates (retained residual sourceRead)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem recovery_balance (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    ‖retained runtime index steps (SourceRecordedEvolution.residual runtime index (steps + 1) target)‖ ^ 2 +
      ‖block runtime index steps target‖ ^ 2 =
    ‖SourceRecordedEvolution.birth runtime index (steps + 1) target‖ ^ 2 +
      ‖retained runtime index (steps + 1) (SourceRecordedEvolution.residual runtime index (steps + 2) target)‖ ^ 2 := by
  have actual := SourceCompleteGraph.energy_step 0 runtime index (steps + 1) target
  rw [← SourceRecordedEvolution.residual_original 0, ← SourceRecordedEvolution.birth_original 0,
    ← SourceRecordedEvolution.residual_original 0] at actual
  have old := SourceCopyFutureCoordinates.original_residual_budget runtime index steps target
  have next := SourceCopyFutureCoordinates.original_residual_budget runtime index (steps + 1) target
  have incoming := block_budget runtime index steps target
  linarith only [actual, old, next, incoming]

theorem gain_budget (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    ‖gain runtime index steps (sourceRead runtime index steps target) (samples runtime index steps target)‖ ^ 2 +
      ‖residual runtime index (steps + 1) target‖ ^ 2 = ‖residual runtime index steps target‖ ^ 2 := by
  rw [gain_source]
  exact block_budget runtime index steps target

end
end SourceCopyFutureUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
