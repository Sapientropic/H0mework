import H0mework.Versions.R30218c1a.Physics.LowEnergyScalarBlock.Fields

/-! The exact source scalar Euler operator for arbitrary scalar-only profiles. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.ScalarBlock
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource StageNineDynamicBreakingVacuum Stage9C.Material.SpinPair
open StageNineP286GaugeConnectionVariationDensity StageNineP286GaugeConnectionActionVariation
open StageNineScalarPointwiseEquation StageNineDiracDualFormNativeScalarVariation
open StageNineP286LinkedActiveScalarPairingSkew SU7MotherLieAlgebra
noncomputable section

def covariantKleinGordon (profile : BasePoint → ScalarCoordinateCarrier)
    (point : BasePoint) : ScalarCoordinateCarrier :=
  (∑ mu, inverseFactor mu • backgroundCovariant (backgroundCovariant profile mu) mu point)+
    (2:ℝ) • profile point

theorem scalar_momentum_derivative (profile : BasePoint → ScalarCoordinateCarrier)
    (parameter : ℝ) (point : BasePoint) (differentiable : Differentiable ℝ profile)
    (test : ScalarCoordinateCarrier) (mu : LorentzianIndex)
    (twice : DifferentiableAt ℝ (backgroundCovariant profile mu) point) :
    fieldDirectionalDerivative
      (scalarDifferentialMomentum positiveSmoothUnifiedSource (configuration profile parameter) test mu)
      point mu = lapse*parameter*inverseFactor mu*scalarCoordinatePairingRe test
        (fieldDirectionalDerivative (backgroundCovariant profile mu) point mu) := by
  have equal : scalarDifferentialMomentum positiveSmoothUnifiedSource
      (configuration profile parameter) test mu =
      fun p => lapse*parameter*inverseFactor mu*scalarCoordinatePairingRe test (backgroundCovariant profile mu p) := by
    funext p
    exact scalar_momentum profile parameter p (differentiable p) test mu
  let pairing := scalarCoordinatePairingReBilinear.toContinuousBilinearMap test
  have derivative := (pairing.hasFDerivAt.comp point twice.hasFDerivAt).const_mul
    (lapse*parameter*inverseFactor mu)
  rw [equal]
  change fieldDirectionalDerivative
    (fun p => lapse*parameter*inverseFactor mu*pairing (backgroundCovariant profile mu p)) point mu = _
  unfold fieldDirectionalDerivative
  change HasFDerivAt
    (fun p => lapse*parameter*inverseFactor mu*pairing (backgroundCovariant profile mu p)) _ point at derivative
  rw [derivative.fderiv]
  rfl

theorem scalar_euler (profile : BasePoint → ScalarCoordinateCarrier) (parameter : ℝ)
    (point : BasePoint) (differentiable : Differentiable ℝ profile)
    (twice : ∀ mu, DifferentiableAt ℝ (backgroundCovariant profile mu) point)
    (test : ScalarCoordinateCarrier) :
    diracDualScalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
      (configuration profile parameter) test point =
        -lapse*parameter*scalarCoordinatePairingRe test (covariantKleinGordon profile point) := by
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient scalarDifferentialMomentumDivergence
  rw [scalar_algebraic profile parameter point (differentiable point)]
  simp_rw [scalar_momentum_derivative profile parameter point differentiable test _ (twice _)]
  have skew (mu : LorentzianIndex) :
      scalarCoordinatePairingRe
        (scalarMotherLieAction (p286LieBlockEmbed (actual.gaugeConnection point mu)) test)
        (backgroundCovariant profile mu point) =
        -scalarCoordinatePairingRe test
          (scalarMotherLieAction (p286LieBlockEmbed (actual.gaugeConnection point mu))
            (backgroundCovariant profile mu point)) := by
    linarith [scalarCoordinatePairingRe_scalarMotherLieAction_skew
      (p286LieBlockEmbed (actual.gaugeConnection point mu)) test (backgroundCovariant profile mu point)]
  simp_rw [skew]
  have sum_pairing (terms : LorentzianIndex → ScalarCoordinateCarrier) :
      scalarCoordinatePairingRe test (∑ mu, terms mu) = ∑ mu, scalarCoordinatePairingRe test (terms mu) :=
    map_sum (scalarCoordinatePairingReBilinear test) terms Finset.univ
  rw [covariantKleinGordon, scalarCoordinatePairingRe_add_right, sum_pairing,
    scalarCoordinatePairingRe_real_smul_right]
  simp_rw [scalarCoordinatePairingRe_real_smul_right, backgroundCovariant,
    scalarCoordinatePairingRe_add_right]
  simp only [Fin.sum_univ_four]
  ring

theorem scalar_euler_first_derivative (profile : BasePoint → ScalarCoordinateCarrier)
    (point : BasePoint) (differentiable : Differentiable ℝ profile)
    (twice : ∀ mu, DifferentiableAt ℝ (backgroundCovariant profile mu) point)
    (test : ScalarCoordinateCarrier) :
    HasDerivAt (fun parameter => diracDualScalarEulerLagrangeDirectionalCoefficient
      positiveSmoothUnifiedSource (configuration profile parameter) test point)
      (-lapse*scalarCoordinatePairingRe test (covariantKleinGordon profile point)) 0 := by
  have equal := funext (fun parameter => scalar_euler profile parameter point differentiable twice test)
  rw [equal]
  convert! ((hasDerivAt_id (0:ℝ)).const_mul (-lapse)).mul_const
    (scalarCoordinatePairingRe test (covariantKleinGordon profile point)) using 1
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.ScalarBlock
