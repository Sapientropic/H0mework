import H0mework.Fock.CopyGraph.FutureCoordinatesKernel
import H0mework.Fock.CopyGraph.CurrentCoordinatesRealization

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyFutureCoordinates

open SourceCopyProgram (Index)
open SourceCopyTimeModel (hilbert mass)
open SourceCopyRecordedRecurrence (cutoff)
open SourceGeneratedAcquisitionContinuation
open SourceOwnedObservationHistory.SourceShift (H basis)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

def hilbertLift (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    (Fin (cutoff runtime index (steps + 1) + 1) → ℂ) →ₗ[ℂ] H :=
  SourceCopyCurrentCoordinates.hilbertLift runtime index (steps + 1)

theorem hilbert_lift_at (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (value : Fin (cutoff runtime index (steps + 1) + 1) → ℂ) (coordinate : Fin (cutoff runtime index (steps + 1) + 1)) :
    hilbertLift runtime index steps value coordinate.val = value coordinate :=
  SourceCopyCurrentCoordinates.hilbert_lift_at runtime index (steps + 1) value coordinate

theorem hilbert_lift_outside (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (value : Fin (cutoff runtime index (steps + 1) + 1) → ℂ) (coordinate : Nat)
    (beyond : cutoff runtime index (steps + 1) < coordinate) :
    hilbertLift runtime index steps value coordinate = 0 :=
  SourceCopyCurrentCoordinates.hilbert_lift_outside runtime index (steps + 1) value coordinate beyond

def realize (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    Coordinates runtime index steps →ₗ[ℂ] SourceJointClockGraph.Carrier :=
  SourceCopyCurrentCoordinates.realize runtime index (steps + 1)

theorem realize_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (value : Coordinates runtime index steps) : sourceRead runtime index steps (realize runtime index steps value) = value :=
  SourceCopyCurrentCoordinates.realize_source runtime index (steps + 1) value

theorem source_surjective (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    Function.Surjective (sourceRead runtime index steps) :=
  SourceCopyCurrentCoordinates.source_surjective runtime index (steps + 1)


end
end SourceCopyFutureCoordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
