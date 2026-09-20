import H0mework.Physics.LowEnergyEvolution.Scalar
import H0mework.Physics.LowEnergyEvolution.Dirac

/-! Spatially dependent radial fields and the original scalar Euler channel.
Every derivative below is the actual holonomic derivative of that field. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Spacetime
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource StageNineDynamicBreakingVacuum Stage9C.Material.SpinPair
open StageNineP286GaugeConnectionVariationDensity StageNineP286GaugeConnectionActionVariation
open StageNineScalarVariation StageNineScalarPointwiseEquation StageNineDiracDualFormNativeScalarVariation
open StageNineP286LinkedActiveScalarPairingSkew Stage9C.Dynamics.Homogeneous
open SU7MotherLieAlgebra Response.Radial
noncomputable section

def configuration (profile : BasePoint → ℝ) (parameter : ℝ) : StageNineHolonomicConfiguration :=
  { actual with scalar := fun point => direction+(parameter*profile point) • direction }

def coordinateDerivative (profile : BasePoint → ℝ) (mu : LorentzianIndex) (point : BasePoint) : ℝ :=
  fieldDirectionalDerivative profile point mu

def inverseFactor : LorentzianIndex → ℝ := ![-(lapse^2)⁻¹,1,1,1]

theorem configuration_zero (profile : BasePoint → ℝ) : configuration profile 0 = actual := by
  apply StageNineHolonomicConfiguration.ext <;> try rfl
  funext point
  simp [configuration, actual_scalar, direction]

theorem scalar_derivative (profile : BasePoint → ℝ) (parameter : ℝ) (point : BasePoint)
    (differentiable : DifferentiableAt ℝ profile point) (mu : LorentzianIndex) :
    fieldDirectionalDerivative (configuration profile parameter).scalar point mu =
      (parameter*coordinateDerivative profile mu point) • direction := by
  have derivative := (hasFDerivAt_const (𝕜 := ℝ) direction point).add
    ((differentiable.hasFDerivAt.const_mul parameter).smul_const direction)
  change HasFDerivAt (fun p : BasePoint => direction+(parameter*profile p) • direction) _ point at derivative
  unfold fieldDirectionalDerivative
  change fderiv ℝ (fun p => direction+(parameter*profile p) • direction) point (coordinateDirection mu) = _
  rw [derivative.fderiv]
  change (0 : ScalarCoordinateCarrier)+(parameter*coordinateDerivative profile mu point) • direction = _
  rw [zero_add]

theorem scalar_covariant (profile : BasePoint → ℝ) (parameter : ℝ) (point : BasePoint)
    (differentiable : DifferentiableAt ℝ profile point) (mu : LorentzianIndex) :
    holonomicScalarCovariantDerivative (configuration profile parameter) point mu =
      (parameter*coordinateDerivative profile mu point) • direction := by
  rw [holonomicScalarCovariantDerivative, scalar_derivative profile parameter point differentiable mu]
  change _+scalarMotherLieAction (p286LieBlockEmbed (actual.gaugeConnection point mu))
    (direction+(parameter*profile point) • direction) = _
  rw [scalarMotherLieAction_add_right, scalarMotherLieAction_real_smul_right,
    background_action_zero, smul_zero, add_zero, add_zero]

private theorem pairing_symmetric (left right : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe left right = scalarCoordinatePairingRe right left := by
  apply Finset.sum_congr rfl
  intro index _
  simp [Complex.mul_re]
  ring

theorem background_test_orthogonal (point : BasePoint) (mu : LorentzianIndex) (test : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe
      (scalarMotherLieAction (p286LieBlockEmbed (actual.gaugeConnection point mu)) test) direction = 0 := by
  have skew := scalarCoordinatePairingRe_scalarMotherLieAction_skew
    (p286LieBlockEmbed (actual.gaugeConnection point mu)) test direction
  rw [background_action_zero] at skew
  simpa [scalarCoordinatePairingRe] using skew

theorem kinetic_first (profile : BasePoint → ℝ) (parameter : ℝ) (point : BasePoint)
    (differentiable : DifferentiableAt ℝ profile point) (variation : LorentzianIndex → ScalarCoordinateCarrier) :
    scalarGaugeConnectionKineticFirstVariationDensity positiveSmoothUnifiedSource 0 point
      (toContinuumPointField (configuration profile parameter) point) variation =
      parameter*∑ mu, inverseFactor mu*coordinateDerivative profile mu point*scalarCoordinatePairingRe (variation mu) direction := by
  have covariant := funext (scalar_covariant profile parameter point differentiable)
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  change (1/2:ℝ)*∑ first, ∑ second, (lorentzianMetricOfCoframe (actual.coframe point))⁻¹ first second *
    (scalarCoordinatePairingRe _ _+scalarCoordinatePairingRe _ _) = _
  rw [Response.ScalarSignature.actual_metric_inverse]
  simp only [scalarFrameRelativeCovariantDerivative, scalarFrameRelativeCoordinates_zeroChart,
    toContinuumPointField, covariant, scalarCoordinatePairingRe_real_smul_left,
    scalarCoordinatePairingRe_real_smul_right]
  simp [Fin.sum_univ_four, Matrix.diagonal_apply, pairing_symmetric direction, inverseFactor]
  ring

theorem scalar_algebraic (profile : BasePoint → ℝ) (parameter : ℝ) (point : BasePoint)
    (differentiable : DifferentiableAt ℝ profile point) (test : ScalarCoordinateCarrier) :
    diracDualScalarAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
      (configuration profile parameter) test point =
      -2*lapse*parameter*profile point*scalarCoordinatePairingRe test direction := by
  have kinetic : scalarGaugeConnectionKineticFirstVariationDensity positiveSmoothUnifiedSource 0 point
      (toContinuumPointField (configuration profile parameter) point)
      (holonomicScalarVariationAlgebraicDirection (configuration profile parameter) test point) = 0 := by
    rw [kinetic_first profile parameter point differentiable]
    change parameter*∑ mu, inverseFactor mu*coordinateDerivative profile mu point*
      scalarCoordinatePairingRe (scalarMotherLieAction (p286LieBlockEmbed (actual.gaugeConnection point mu)) test) direction = 0
    simp only [background_test_orthogonal, mul_zero, Finset.sum_const_zero]
  have potential : scalarPotentialFirstVariation positiveSmoothUnifiedSource
      (toContinuumPointField (configuration profile parameter) point) test =
      2*parameter*profile point*scalarCoordinatePairingRe test direction := by
    unfold scalarPotentialFirstVariation frameRelativeScalarGradient
    change 2*scalarCoordinateRealPairing (direction+(parameter*profile point) • direction-direction) test = _
    rw [add_sub_cancel_left]
    change 2*scalarCoordinatePairingRe ((parameter*profile point) • direction) test = _
    rw [scalarCoordinatePairingRe_real_smul_left, pairing_symmetric direction test]
    ring
  have yukawa : diracDualScalarYukawaFirstVariationDensity
      (toContinuumPointField (configuration profile parameter) point) test = 0 := by
    unfold diracDualScalarYukawaFirstVariationDensity diracDualScalarYukawaVariationVector
    change ((actual.conjugateMatter point) _).re = 0
    rw [actual_conjugateMatter, spinPairDual_yukawa_annihilates]
    rfl
  unfold diracDualScalarAlgebraicDirectionalCoefficient
  rw [kinetic, potential, yukawa]
  change |(actual.coframe point).det| * _ = _
  rw [actual_coframe, homogeneousCoframe_det, abs_of_pos lapse_pos]
  ring

theorem scalar_momentum (profile : BasePoint → ℝ) (parameter : ℝ) (point : BasePoint)
    (differentiable : DifferentiableAt ℝ profile point) (test : ScalarCoordinateCarrier) (mu : LorentzianIndex) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource (configuration profile parameter) test mu point =
      lapse*parameter*inverseFactor mu*coordinateDerivative profile mu point*scalarCoordinatePairingRe test direction := by
  unfold scalarDifferentialMomentum
  rw [kinetic_first profile parameter point differentiable]
  change |(actual.coframe point).det| * _ = _
  rw [actual_coframe, homogeneousCoframe_det, abs_of_pos lapse_pos]
  have pairing (nu : LorentzianIndex) :
      scalarCoordinatePairingRe (scalarVariationDifferentialDirection test mu nu) direction =
        if nu = mu then scalarCoordinatePairingRe test direction else 0 := by
    by_cases same : nu = mu <;> simp [scalarVariationDifferentialDirection, same, scalarCoordinatePairingRe]
  simp_rw [pairing]
  simp
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.Spacetime
