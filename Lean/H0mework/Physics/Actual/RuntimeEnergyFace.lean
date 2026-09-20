import H0mework.Physics.Actual.RuntimeInquiry
import H0mework.Physics.Actual.WeakUniqueness
import H0mework.Foundation.Semantics.SourceUniqueness

/-! The complete weak-candidate fibre enters the original root's analytic
lock at the next registered visit after the accepted classical read. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9CU.Runtime

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Stage9C.Revision

noncomputable section

def energyFace : SourceRootedActualEnergyFaceAt
    SpinPair.livingRoot (SpinPair.visit 2) Weak.Payload where
  entry := materialEntry (SpinPair.support (SpinPair.visit 2).current)
  standing := SpinPair.authorityAt 2
  projection := .weakActual
  active := PUnit.unit
  classified := rfl
  density := Weak.density
  density_injective := Weak.density_injective

theorem pairwiseEnergyZero : energyFace.PairwiseDifferenceEnergyZeroAt :=
  Weak.pairwise_distanceSquared_zero

set_option linter.defProp false in
def sourceRootedUniquenessUnlock := energyFace.unlock pairwiseEnergyZero

theorem canonicalActual_eq : energyFace.canonicalActual = Weak.canonical := rfl

end
end SaturationMonoid.PhysicsCore.Stage9CU.Runtime
