import H0mework.Versions.X.Fock.CopyGraph.SharedNextSourceStepProjection

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeSharedUpdate

open SourceCopyCurrentCoordinates (jointObserver jointModelEquiv)
open SourceGeneratedActionObservationHistory (Model)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def modelStep (runtime : LivingRuntimeState process)
    (previous : Model SourceJointClockGraph.action.toLinearMap (jointObserver runtime)) :
    Model SourceJointClockGraph.action.toLinearMap (jointObserver runtime.tick.next) :=
  (jointModelEquiv runtime.tick.next).symm (step runtime (jointModelEquiv runtime previous))

end
end SourceCopyNativeSharedUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
