import H0mework.Versions.X.Fock.CopyGraph.FutureCoordinatesModel
import H0mework.Versions.X.Fock.CopyGraph.CurrentCoordinatesDimension

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyFutureCoordinates

open SourceCopyProgram (Index)
open SourceCopyRecordedRecurrence (cutoff)
open SourceCopyTemporalBoundary (observer)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem model_dimension (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    Module.finrank ℂ (Model SourceJointClockGraph.action.toLinearMap (observer runtime index (steps + 1))) =
      cutoff runtime index (steps + 1) + 3 :=
  SourceCopyCurrentCoordinates.model_dimension runtime index (steps + 1)


end
end SourceCopyFutureCoordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
