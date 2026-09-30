import H0mework.Versions.X.Fock.CopyGraph.FutureCoordinatesDimension
import H0mework.Versions.X.Fock.CopyGraph.CurrentCoordinatesRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyFutureCoordinates

open SourceCopyProgram (Index)
open SourceCopyRecordedRecurrence (windowBound hidden)
open SourceCopyTemporalBoundary (recordedPrefix)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem window_reconstruction (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    realize runtime index steps (decode runtime index steps
      (recordedPrefix runtime index (steps + 1) (windowBound runtime index (steps + 1)) target)) +
        residual runtime index steps target = target :=
  SourceCopyCurrentCoordinates.window_reconstruction runtime index (steps + 1) target

theorem window_energy (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    ‖realize runtime index steps (decode runtime index steps
      (recordedPrefix runtime index (steps + 1) (windowBound runtime index (steps + 1)) target))‖ ^ 2 +
        ‖residual runtime index steps target‖ ^ 2 = ‖target‖ ^ 2 :=
  SourceCopyCurrentCoordinates.window_energy runtime index (steps + 1) target

theorem hidden_retained (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    retained runtime index steps (hidden runtime index (steps + 1)) = 0 :=
  SourceCopyCurrentCoordinates.hidden_retained runtime index (steps + 1)

theorem hidden_residual (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    residual runtime index steps (hidden runtime index (steps + 1)) = hidden runtime index (steps + 1) :=
  SourceCopyCurrentCoordinates.hidden_residual runtime index (steps + 1)


end
end SourceCopyFutureCoordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
