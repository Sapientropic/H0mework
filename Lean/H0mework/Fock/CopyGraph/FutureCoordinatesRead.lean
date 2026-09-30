import H0mework.Fock.CopyGraph.FutureCoordinatesWindow
import H0mework.Fock.CopyGraph.CurrentCoordinatesRead

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyFutureCoordinates

open SourceCopyProgram (Index)
open SourceCopyTimeModel (time hilbert mass)
open SourceCopyRecordedRecurrence (cutoff windowBound)
open SourceCopyTemporalBoundary (recordedPrefix)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section

def coordinatePhase (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (coordinate : Fin (cutoff runtime index (steps + 1) + 1)) : Fin (windowBound runtime index (steps + 1) + 1) :=
  SourceCopyCurrentCoordinates.coordinatePhase runtime index (steps + 1) coordinate

def hilbertRead (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (coordinate : Fin (cutoff runtime index (steps + 1) + 1)) : Window runtime index steps →ₗ[ℂ] ℂ :=
  SourceCopyCurrentCoordinates.hilbertRead runtime index (steps + 1) coordinate

theorem hilbert_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (coordinate : Fin (cutoff runtime index (steps + 1) + 1)) (target : SourceJointClockGraph.Carrier) :
    hilbertRead runtime index steps coordinate
        (recordedPrefix runtime index (steps + 1) (windowBound runtime index (steps + 1)) target) = hilbert target coordinate.val :=
  SourceCopyCurrentCoordinates.hilbert_source runtime index (steps + 1) coordinate target

abbrev Coordinates (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :=
  (Fin (cutoff runtime index (steps + 1) + 1) → ℂ) × ℂ × ℂ

def decode (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    Window runtime index steps →ₗ[ℂ] Coordinates runtime index steps :=
  SourceCopyCurrentCoordinates.decode runtime index (steps + 1)

def sourceRead (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    SourceJointClockGraph.Carrier →ₗ[ℂ] Coordinates runtime index steps :=
  SourceCopyCurrentCoordinates.sourceRead runtime index (steps + 1)

theorem decode_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    decode runtime index steps (recordedPrefix runtime index (steps + 1) (windowBound runtime index (steps + 1)) target) =
      sourceRead runtime index steps target :=
  SourceCopyCurrentCoordinates.decode_source runtime index (steps + 1) target


end
end SourceCopyFutureCoordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
