import H0mework.Physics.LowEnergyEvolution.Scalar
import H0mework.Physics.LowEnergyEvolution.Dirac

/-! The original scalar field displaced in an arbitrary real direction of its complex carrier. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.ScalarBlock
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource StageNineDynamicBreakingVacuum Stage9C.Material.SpinPair
open StageNineP286GaugeConnectionVariationDensity StageNineP286GaugeConnectionActionVariation
open StageNineScalarVariation StageNineScalarPointwiseEquation StageNineDiracDualFormNativeScalarVariation
open StageNineP286LinkedActiveScalarPairingSkew Stage9C.Dynamics.Homogeneous
open SU7MotherLieAlgebra Response.Radial
noncomputable section

def configuration (profile : BasePoint → ScalarCoordinateCarrier) (parameter : ℝ) :
    StageNineHolonomicConfiguration :=
  { actual with scalar := fun point => direction+parameter • profile point }

def backgroundCovariant (profile : BasePoint → ScalarCoordinateCarrier)
    (mu : LorentzianIndex) (point : BasePoint) : ScalarCoordinateCarrier :=
  fieldDirectionalDerivative profile point mu+
    scalarMotherLieAction (p286LieBlockEmbed (actual.gaugeConnection point mu)) (profile point)

def inverseFactor : LorentzianIndex → ℝ := ![-(lapse^2)⁻¹,1,1,1]

theorem configuration_zero (profile : BasePoint → ScalarCoordinateCarrier) :
    configuration profile 0 = actual := by
  apply StageNineHolonomicConfiguration.ext <;> try rfl
  funext point
  simp [configuration, actual_scalar, direction]

theorem pairing_symmetric (left right : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe left right = scalarCoordinatePairingRe right left := by
  apply Finset.sum_congr rfl
  intro index _
  simp [Complex.mul_re]
  ring

theorem scalar_derivative (profile : BasePoint → ScalarCoordinateCarrier) (parameter : ℝ)
    (point : BasePoint) (differentiable : DifferentiableAt ℝ profile point) (mu : LorentzianIndex) :
    fieldDirectionalDerivative (configuration profile parameter).scalar point mu =
      parameter • fieldDirectionalDerivative profile point mu := by
  have derivative := (hasFDerivAt_const (𝕜 := ℝ) direction point).add
    (differentiable.hasFDerivAt.const_smul parameter)
  change HasFDerivAt (fun p : BasePoint => direction+parameter • profile p) _ point at derivative
  unfold fieldDirectionalDerivative
  change fderiv ℝ (fun p => direction+parameter • profile p) point (coordinateDirection mu) = _
  rw [derivative.fderiv]
  change (0 : ScalarCoordinateCarrier)+parameter • _ = _
  rw [zero_add]
  rfl

theorem scalar_covariant (profile : BasePoint → ScalarCoordinateCarrier) (parameter : ℝ)
    (point : BasePoint) (differentiable : DifferentiableAt ℝ profile point) (mu : LorentzianIndex) :
    holonomicScalarCovariantDerivative (configuration profile parameter) point mu =
      parameter • backgroundCovariant profile mu point := by
  rw [holonomicScalarCovariantDerivative, scalar_derivative profile parameter point differentiable mu]
  change _+scalarMotherLieAction (p286LieBlockEmbed (actual.gaugeConnection point mu))
    (direction+parameter • profile point) = _
  rw [scalarMotherLieAction_add_right, scalarMotherLieAction_real_smul_right,
    background_action_zero, zero_add, ← smul_add]
  rfl

theorem kinetic_first (profile : BasePoint → ScalarCoordinateCarrier) (parameter : ℝ)
    (point : BasePoint) (differentiable : DifferentiableAt ℝ profile point)
    (variation : LorentzianIndex → ScalarCoordinateCarrier) :
    scalarGaugeConnectionKineticFirstVariationDensity positiveSmoothUnifiedSource 0 point
      (toContinuumPointField (configuration profile parameter) point) variation =
      parameter*∑ mu, inverseFactor mu*
        scalarCoordinatePairingRe (variation mu) (backgroundCovariant profile mu point) := by
  have covariant := funext (scalar_covariant profile parameter point differentiable)
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  change (1/2:ℝ)*∑ first, ∑ second, (lorentzianMetricOfCoframe (actual.coframe point))⁻¹ first second *
    (scalarCoordinatePairingRe _ _+scalarCoordinatePairingRe _ _) = _
  rw [Response.ScalarSignature.actual_metric_inverse]
  simp only [scalarFrameRelativeCovariantDerivative, scalarFrameRelativeCoordinates_zeroChart,
    toContinuumPointField, covariant, scalarCoordinatePairingRe_real_smul_left,
    scalarCoordinatePairingRe_real_smul_right]
  simp [Fin.sum_univ_four, Matrix.diagonal_apply, inverseFactor,
    pairing_symmetric (backgroundCovariant profile 0 point),
    pairing_symmetric (backgroundCovariant profile 1 point),
    pairing_symmetric (backgroundCovariant profile 2 point),
    pairing_symmetric (backgroundCovariant profile 3 point)]
  ring

theorem scalar_potential (profile : BasePoint → ScalarCoordinateCarrier) (parameter : ℝ)
    (point : BasePoint) (test : ScalarCoordinateCarrier) :
    scalarPotentialFirstVariation positiveSmoothUnifiedSource
      (toContinuumPointField (configuration profile parameter) point) test =
      2*parameter*scalarCoordinatePairingRe test (profile point) := by
  unfold scalarPotentialFirstVariation frameRelativeScalarGradient
  change 2*scalarCoordinateRealPairing (direction+parameter • profile point-direction) test = _
  rw [add_sub_cancel_left]
  change 2*scalarCoordinatePairingRe (parameter • profile point) test = _
  rw [scalarCoordinatePairingRe_real_smul_left, pairing_symmetric (profile point) test]
  ring

theorem scalar_yukawa (profile : BasePoint → ScalarCoordinateCarrier) (parameter : ℝ)
    (point : BasePoint) (test : ScalarCoordinateCarrier) :
    diracDualScalarYukawaFirstVariationDensity
      (toContinuumPointField (configuration profile parameter) point) test = 0 := by
  unfold diracDualScalarYukawaFirstVariationDensity diracDualScalarYukawaVariationVector
  change ((actual.conjugateMatter point) _).re = 0
  rw [actual_conjugateMatter, spinPairDual_yukawa_annihilates]
  rfl

theorem scalar_algebraic (profile : BasePoint → ScalarCoordinateCarrier) (parameter : ℝ)
    (point : BasePoint) (differentiable : DifferentiableAt ℝ profile point)
    (test : ScalarCoordinateCarrier) :
    diracDualScalarAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
      (configuration profile parameter) test point =
      lapse*parameter*((∑ mu, inverseFactor mu*scalarCoordinatePairingRe
        (scalarMotherLieAction (p286LieBlockEmbed (actual.gaugeConnection point mu)) test)
        (backgroundCovariant profile mu point))-2*scalarCoordinatePairingRe test (profile point)) := by
  unfold diracDualScalarAlgebraicDirectionalCoefficient
  rw [kinetic_first profile parameter point differentiable, scalar_potential, scalar_yukawa]
  change |(actual.coframe point).det| * _ = _
  rw [actual_coframe, homogeneousCoframe_det, abs_of_pos lapse_pos]
  change lapse*(parameter*(∑ mu, inverseFactor mu*scalarCoordinatePairingRe
    (scalarMotherLieAction (p286LieBlockEmbed (actual.gaugeConnection point mu)) test)
    (backgroundCovariant profile mu point))-2*parameter*scalarCoordinatePairingRe test (profile point)+0) = _
  ring

theorem scalar_momentum (profile : BasePoint → ScalarCoordinateCarrier) (parameter : ℝ)
    (point : BasePoint) (differentiable : DifferentiableAt ℝ profile point)
    (test : ScalarCoordinateCarrier) (mu : LorentzianIndex) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource (configuration profile parameter) test mu point =
      lapse*parameter*inverseFactor mu*scalarCoordinatePairingRe test (backgroundCovariant profile mu point) := by
  unfold scalarDifferentialMomentum
  rw [kinetic_first profile parameter point differentiable]
  change |(actual.coframe point).det| * _ = _
  rw [actual_coframe, homogeneousCoframe_det, abs_of_pos lapse_pos]
  have pairing (nu : LorentzianIndex) :
      scalarCoordinatePairingRe (scalarVariationDifferentialDirection test mu nu)
        (backgroundCovariant profile nu point) =
        if nu = mu then scalarCoordinatePairingRe test (backgroundCovariant profile mu point) else 0 := by
    by_cases same : nu = mu <;> simp [scalarVariationDifferentialDirection, same, scalarCoordinatePairingRe]
  simp_rw [pairing]
  simp
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.ScalarBlock
