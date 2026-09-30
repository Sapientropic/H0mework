import H0mework.Fock.CopyGraph.FutureCoordinatesInvisible
import H0mework.Fock.CopyGraph.CurrentCoordinatesKernel

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyFutureCoordinates

open SourceCopyProgram (Index)
open SourceCopyTimeModel (time hilbert mass)
open SourceCopyRecordedRecurrence (cutoff windowBound)
open SourceCopyTemporalBoundary (observer)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open SourceOwnedObservationHistory.SourceShift (H)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem kernel_exact (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    LinearMap.ker (sourceMap SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 1))) =
      LinearMap.ker (sourceRead runtime index steps) :=
  SourceCopyCurrentCoordinates.kernel_exact runtime index (steps + 1)

theorem model_coordinates (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (left right : SourceJointClockGraph.Carrier) :
    projection SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 1)) left =
        projection SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 1)) right ↔
      sourceRead runtime index steps left = sourceRead runtime index steps right :=
  SourceCopyCurrentCoordinates.model_coordinates runtime index (steps + 1) left right

theorem complete_fibre (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (left right : SourceJointClockGraph.Carrier) :
    left = right ↔ sourceRead runtime index steps left = sourceRead runtime index steps right ∧
      ∀ coordinate : Nat, cutoff runtime index (steps + 1) < coordinate → hilbert left coordinate = hilbert right coordinate :=
  SourceCopyCurrentCoordinates.complete_fibre runtime index (steps + 1) left right


end
end SourceCopyFutureCoordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
