import H0mework.Fock.CopyGraph.CurrentCoordinatesModel

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyCurrentCoordinates

open SourceCopyProgram (Index)
open SourceCopyRecordedRecurrence (cutoff)
open SourceCopyTemporalBoundary (observer)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem model_dimension (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat) :
    Module.finrank ℂ (Model SourceJointClockGraph.action.toLinearMap (observer runtime index steps)) =
      cutoff runtime index steps + 3 := by
  rw [(modelEquiv runtime index steps).finrank_eq]
  simp only [Coordinates, Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self]

end
end SourceCopyCurrentCoordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
