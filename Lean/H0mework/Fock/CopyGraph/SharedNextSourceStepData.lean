import H0mework.Fock.CopyGraph.SharedNextFlow

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyNativeSharedUpdate

open SourceCopyCurrentCoordinates (Coordinates maximumIndex sourceRead realize)
open SourceCopyTimeModel (time)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def step (runtime : LivingRuntimeState process) (previous : Coordinates runtime (maximumIndex runtime) 0) :
    Coordinates runtime.tick.next (maximumIndex runtime.tick.next) 0 :=
  sourceRead runtime.tick.next (maximumIndex runtime.tick.next) 0
    (SourceJointClockGraph.action (realize runtime (maximumIndex runtime) 0 previous))

def trajectory (runtime : LivingRuntimeState process) (initial : Coordinates runtime (maximumIndex runtime) 0) (stage : Nat) :
    Coordinates (runtime.advance stage) (maximumIndex (runtime.advance stage)) 0 :=
  sourceRead (runtime.advance stage) (maximumIndex (runtime.advance stage)) 0
    (time stage (realize runtime (maximumIndex runtime) 0 initial))

end
end SourceCopyNativeSharedUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
