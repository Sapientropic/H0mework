import H0mework.Physics.LowEnergySpacetime.ScalarField

/-! The spacetime radial operator read directly from the original scalar equation. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Spacetime
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource StageNineDynamicBreakingVacuum Stage9C.Material.SpinPair
open StageNineScalarPointwiseEquation StageNineDiracDualFormNativeScalarVariation
open Stage9C.Dynamics.Homogeneous Response.Radial
noncomputable section

theorem scalar_momentum_derivative (profile : BasePoint → ℝ) (parameter : ℝ)
    (point : BasePoint) (differentiable : Differentiable ℝ profile)
    (test : ScalarCoordinateCarrier) (mu : LorentzianIndex)
    (twice : DifferentiableAt ℝ (coordinateDerivative profile mu) point) :
    fieldDirectionalDerivative
      (scalarDifferentialMomentum positiveSmoothUnifiedSource (configuration profile parameter) test mu)
      point mu = lapse*parameter*inverseFactor mu*
        coordinateDerivative (coordinateDerivative profile mu) mu point*
          scalarCoordinatePairingRe test direction := by
  have equal : scalarDifferentialMomentum positiveSmoothUnifiedSource
      (configuration profile parameter) test mu =
      fun p => lapse*parameter*inverseFactor mu*coordinateDerivative profile mu p*
        scalarCoordinatePairingRe test direction := by
    funext p
    exact scalar_momentum profile parameter p (differentiable p) test mu
  have derivative := (twice.hasFDerivAt.const_mul (lapse*parameter*inverseFactor mu)).mul_const
    (scalarCoordinatePairingRe test direction)
  rw [equal]
  unfold fieldDirectionalDerivative
  rw [derivative.fderiv]
  simp only [smul_apply, smul_eq_mul]
  change _ = lapse*parameter*inverseFactor mu*
    (fderiv ℝ (coordinateDerivative profile mu) point (coordinateDirection mu))*
      scalarCoordinatePairingRe test direction
  ring

def radialOperator (profile : BasePoint → ℝ) (point : BasePoint) : ℝ :=
  coordinateDerivative (coordinateDerivative profile 0) 0 point/lapse^2-
    (∑ axis : Fin 3, coordinateDerivative (coordinateDerivative profile axis.succ) axis.succ point)-
      2*profile point

theorem scalar_euler (profile : BasePoint → ℝ) (parameter : ℝ) (point : BasePoint)
    (differentiable : Differentiable ℝ profile)
    (twice : ∀ mu, DifferentiableAt ℝ (coordinateDerivative profile mu) point)
    (test : ScalarCoordinateCarrier) :
    diracDualScalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
      (configuration profile parameter) test point =
        lapse*parameter*radialOperator profile point*scalarCoordinatePairingRe test direction := by
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient scalarDifferentialMomentumDivergence
  rw [scalar_algebraic profile parameter point (differentiable point)]
  simp_rw [scalar_momentum_derivative profile parameter point differentiable test _ (twice _)]
  simp [radialOperator, inverseFactor, Fin.sum_univ_four, Fin.sum_univ_three]
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.Spacetime
