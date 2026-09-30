import H0mework.Fock.CopyGraph.FutureCoordinatesRecovery
import H0mework.Fock.CopyGraph.CurrentCoordinatesAccount

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyFutureCoordinates

open SourceCopyProgram (Index)
open SourceCopyTemporalBoundary (observer)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section
attribute [local instance] SourceCopyCofinal.finiteComplete

theorem current_prediction_tail_zero (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    residual runtime index steps (SourceCopyGraph.action (inventoryBound runtime) index (observer runtime index (steps + 1) target)) = 0 :=
  SourceCopyCurrentCoordinates.current_prediction_tail_zero runtime index (steps + 1) target

theorem original_residual_tail (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    residual runtime index steps (SourceRecordedEvolution.residual runtime index (steps + 1) target) =
      residual runtime index steps target :=
  SourceCopyCurrentCoordinates.original_residual_tail runtime index (steps + 1) target

theorem original_residual_partition (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    retained runtime index steps (SourceRecordedEvolution.residual runtime index (steps + 1) target) +
      residual runtime index steps target = SourceRecordedEvolution.residual runtime index (steps + 1) target :=
  SourceCopyCurrentCoordinates.original_residual_partition runtime index (steps + 1) target

theorem original_residual_budget (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    ‖retained runtime index steps (SourceRecordedEvolution.residual runtime index (steps + 1) target)‖ ^ 2 +
      ‖residual runtime index steps target‖ ^ 2 = ‖SourceRecordedEvolution.residual runtime index (steps + 1) target‖ ^ 2 :=
  SourceCopyCurrentCoordinates.original_residual_budget runtime index (steps + 1) target

theorem history_budget (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    ‖retained runtime index steps (SourceRecordedEvolution.residual runtime index (steps + 1) target)‖ ^ 2 +
      ‖residual runtime index steps target‖ ^ 2 +
      ∑ stage ∈ Finset.range (steps + 1), ‖SourceRecordedEvolution.birth runtime index stage target‖ ^ 2 =
        ‖SourceRecordedEvolution.residual runtime index 0 target‖ ^ 2 :=
  SourceCopyCurrentCoordinates.history_budget runtime index (steps + 1) target


end
end SourceCopyFutureCoordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
