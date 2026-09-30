import H0mework.Fock.SourceHistory.InverseObservationNative.Native

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInverseObservationBirth

def birth {Key : Type*} [DecidableEq Key] (read : Nat → Key) (bound : Nat) (program : Nat × Nat) (steps : Nat)
    (previous : SourceInverseDistributionStream.State Key bound) : SourceInverseDistributionStream.State Key (bound + 1) :=
  SourceInverseObservationNative.fromState (bound + 1) program steps
    (SourceConditionalNativeObservers.advance read bound (SourceInverseDistributionStream.source bound previous))

end SourceInverseObservationBirth
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
