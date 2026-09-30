import H0mework.Versions.X.Fock.CopyGraph.FutureAcquisitionObservation
import H0mework.Versions.X.Fock.CopyGraph.CurrentCoordinatesSource

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

theorem observed_column (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (target : SourceJointClockGraph.Carrier) :
    ⟪SourceColumnForcing.column (inventoryBound runtime) index (inventoryBound runtime + steps + 1),
      SourceCopyGraph.action (inventoryBound runtime) index (observer runtime index (steps + 1) target)⟫_ℂ =
        ⟪SourceColumnForcing.column (inventoryBound runtime) index (inventoryBound runtime + steps + 1), target⟫_ℂ :=
  SourceCopyCurrentCoordinates.observed_column runtime index (steps + 1) target


end
end SourceCopyFutureCoordinates
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
