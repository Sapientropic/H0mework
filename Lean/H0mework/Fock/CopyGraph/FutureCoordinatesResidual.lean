import H0mework.Fock.CopyGraph.FutureCoordinatesRealization
import H0mework.Fock.CopyGraph.CurrentCoordinatesResidual

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyFutureCoordinates

open SourceCopyProgram (Index)
open SourceCopyTimeModel (hilbert mass)
open SourceCopyRecordedRecurrence (cutoff windowBound)
open SourceCopyTemporalBoundary (recordedPrefix)
open SourceGeneratedAcquisitionContinuation
open SourceOwnedObservationHistory.SourceShift (basis)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section

def retained (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    SourceJointClockGraph.Carrier →ₗ[ℂ] SourceJointClockGraph.Carrier :=
  SourceCopyCurrentCoordinates.retained runtime index (steps + 1)

def residual (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    SourceJointClockGraph.Carrier →ₗ[ℂ] SourceJointClockGraph.Carrier :=
  SourceCopyCurrentCoordinates.residual runtime index (steps + 1)

theorem reconstruction (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    retained runtime index steps target + residual runtime index steps target = target :=
  SourceCopyCurrentCoordinates.reconstruction runtime index (steps + 1) target

theorem window_recovery (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    realize runtime index steps (decode runtime index steps
      (recordedPrefix runtime index (steps + 1) (windowBound runtime index (steps + 1)) target)) = retained runtime index steps target :=
  SourceCopyCurrentCoordinates.window_recovery runtime index (steps + 1) target

theorem residual_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) : sourceRead runtime index steps (residual runtime index steps target) = 0 :=
  SourceCopyCurrentCoordinates.residual_source runtime index (steps + 1) target

theorem residual_inside (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) (coordinate : Fin (cutoff runtime index (steps + 1) + 1)) :
    hilbert (residual runtime index steps target) coordinate.val = 0 :=
  SourceCopyCurrentCoordinates.residual_inside runtime index (steps + 1) target coordinate

theorem residual_outside (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) (coordinate : Nat) (beyond : cutoff runtime index (steps + 1) < coordinate) :
    hilbert (residual runtime index steps target) coordinate = hilbert target coordinate :=
  SourceCopyCurrentCoordinates.residual_outside runtime index (steps + 1) target coordinate beyond

theorem retained_orthogonal (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (left right : SourceJointClockGraph.Carrier) :
    ⟪retained runtime index steps left, residual runtime index steps right⟫_ℂ = 0 :=
  SourceCopyCurrentCoordinates.retained_orthogonal runtime index (steps + 1) left right

theorem energy (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    ‖retained runtime index steps target‖ ^ 2 + ‖residual runtime index steps target‖ ^ 2 = ‖target‖ ^ 2 :=
  SourceCopyCurrentCoordinates.energy runtime index (steps + 1) target


end
end SourceCopyFutureCoordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
