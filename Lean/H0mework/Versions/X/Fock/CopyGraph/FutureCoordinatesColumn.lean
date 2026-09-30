import H0mework.Versions.X.Fock.CopyGraph.FutureCoordinatesSource
import H0mework.Versions.X.Fock.CopyGraph.CurrentCoordinatesColumn

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyFutureCoordinates

open SourceCopyProgram (Index indexAfter)
open SourceCopyTimeModel (time hilbert mass)
open SourceCopyRecordedRecurrence (cutoff)
open SourceGeneratedAcquisitionContinuation SourceSuccessorBoundary
open SourceOwnedObservationHistory.SourceShift (basis)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section

theorem column_pairing (depth : Nat) (index : Index depth) (actor : Nat) (target : SourceJointClockGraph.Carrier) :
    ⟪SourceColumnForcing.column depth index actor, target⟫_ℂ =
      hilbert target (indexAfter depth index actor) + mass target +
        ((indexAfter depth index actor + 1 : Nat) : ℂ) * SourceJointClockGraph.clock target :=
  SourceCopyCurrentCoordinates.column_pairing depth index actor target

theorem tail_pairing (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps ticks : Nat)
    (beyond : cutoff runtime index (steps + 1) < ticks) (target : SourceJointClockGraph.Carrier) :
    ⟪SourceColumnForcing.column (inventoryBound runtime) index (inventoryBound runtime + steps + 1), time ticks target⟫_ℂ =
      mass target + ((cutoff runtime index (steps + 1) + 1 : Nat) : ℂ) *
        (SourceJointClockGraph.clock target + (ticks : ℂ) * mass target) :=
  SourceCopyCurrentCoordinates.tail_pairing runtime index (steps + 1) ticks beyond target

theorem tail_difference (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    ⟪SourceColumnForcing.column (inventoryBound runtime) index (inventoryBound runtime + steps + 1),
      time (cutoff runtime index (steps + 1) + 2) target⟫_ℂ -
    ⟪SourceColumnForcing.column (inventoryBound runtime) index (inventoryBound runtime + steps + 1),
      time (cutoff runtime index (steps + 1) + 1) target⟫_ℂ =
        ((cutoff runtime index (steps + 1) + 1 : Nat) : ℂ) * mass target :=
  SourceCopyCurrentCoordinates.tail_difference runtime index (steps + 1) target


end
end SourceCopyFutureCoordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
