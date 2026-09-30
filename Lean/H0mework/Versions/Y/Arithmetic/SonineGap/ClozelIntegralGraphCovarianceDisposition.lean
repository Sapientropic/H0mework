import H0mework.Realization.Coherent.CovarianceNaturality
import H0mework.Versions.Y.Arithmetic.RiemannGraph.IntegralGraphCouplingResidual

/-!
# Integral graph orbit as a generic covariance system

The existing selected/reversal integral graph orbits directly instantiate the
source-neutral integral/coherent covariance producer.  Its event residual is
definitionally the already generated owner-free coupling residual.  Thus the
generic total disposition is consumed without adding a character, zero, or
neutrality field to the owner-free action.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace CenteredGram

open SourceGeneratedIntegralCoherentCovariance
open Character.GlobalCoPoissonCurrent
open SourceGeneratedIntegralCharacterGroupRing
open ThetaJRoleRepresentation

noncomputable section

def selectedIntegralGraphCovarianceAction
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    ActionData (selectedIntegralGraphOrbit observation nontrivial) where
  integralTransition := (leftTranslation scale).toLinearMap
  hilbertEvolution :=
    (positiveMellinQuarterGraphTargetIsometry
      (Real.log (scaleSquare scale))).toLinearIsometry

def reversalIntegralGraphCovarianceAction
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    ActionData (reversalIntegralGraphOrbit observation nontrivial) where
  integralTransition := (leftTranslation scale).toLinearMap
  hilbertEvolution :=
    (positiveMellinQuarterGraphTargetIsometry
      (Real.log (scaleSquare scale))).toLinearIsometry

theorem selectedIntegralGraphCovariance_couplingResidual
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) (event : IntegralScaleCarrier) :
    couplingResidual
        (selectedIntegralGraphCovarianceAction
          observation nontrivial scale) event =
      selectedOwnerFreeCouplingResidual
        observation nontrivial scale event := by
  rfl

theorem reversalIntegralGraphCovariance_couplingResidual
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) (event : IntegralScaleCarrier) :
    couplingResidual
        (reversalIntegralGraphCovarianceAction
          observation nontrivial scale) event =
      reversalOwnerFreeCouplingResidual
        observation nontrivial scale event := by
  rfl

/-- Generic total disposition on the selected sibling face. -/
def selectedIntegralGraphCovarianceDisposition
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    CovarianceDisposition
      (selectedIntegralGraphCovarianceAction observation nontrivial scale) :=
  settleCovariance
    (selectedIntegralGraphCovarianceAction observation nontrivial scale)

/-- Generic total disposition on the reversal sibling face. -/
def reversalIntegralGraphCovarianceDisposition
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    CovarianceDisposition
      (reversalIntegralGraphCovarianceAction observation nontrivial scale) :=
  settleCovariance
    (reversalIntegralGraphCovarianceAction observation nontrivial scale)

end


end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
