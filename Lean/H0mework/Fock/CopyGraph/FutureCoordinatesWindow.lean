import H0mework.Fock.CopyGraph.FutureCoordinatesColumn
import H0mework.Fock.CopyGraph.CurrentCoordinatesWindow

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyFutureCoordinates

open SourceCopyProgram (Index)
open SourceCopyTimeModel (time mass)
open SourceCopyRecordedRecurrence (cutoff windowBound priorIndex)
open SourceCopyTemporalBoundary (recordedPrefix)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section

abbrev Window (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :=
  PrefixCarrier SourceJointClockGraph.Carrier (windowBound runtime index (steps + 1))

def response (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (phase : Fin (windowBound runtime index (steps + 1) + 1)) : Window runtime index steps →ₗ[ℂ] ℂ :=
  SourceCopyCurrentCoordinates.response runtime index (steps + 1) phase

theorem response_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (phase : Fin (windowBound runtime index (steps + 1) + 1)) (target : SourceJointClockGraph.Carrier) :
    response runtime index steps phase (recordedPrefix runtime index (steps + 1) (windowBound runtime index (steps + 1)) target) =
      ⟪SourceColumnForcing.column (inventoryBound runtime) index (inventoryBound runtime + steps + 1), time phase.val target⟫_ℂ :=
  SourceCopyCurrentCoordinates.response_source runtime index (steps + 1) phase target

def massRead (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    Window runtime index steps →ₗ[ℂ] ℂ :=
  SourceCopyCurrentCoordinates.massRead runtime index (steps + 1)

theorem mass_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    massRead runtime index steps
        (recordedPrefix runtime index (steps + 1) (windowBound runtime index (steps + 1)) target) = mass target :=
  SourceCopyCurrentCoordinates.mass_source runtime index (steps + 1) target

def clockRead (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    Window runtime index steps →ₗ[ℂ] ℂ :=
  SourceCopyCurrentCoordinates.clockRead runtime index (steps + 1)

theorem clock_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    clockRead runtime index steps
        (recordedPrefix runtime index (steps + 1) (windowBound runtime index (steps + 1)) target) = SourceJointClockGraph.clock target :=
  SourceCopyCurrentCoordinates.clock_source runtime index (steps + 1) target


end
end SourceCopyFutureCoordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
