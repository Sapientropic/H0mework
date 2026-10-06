import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.GreenRegularity
import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.SmoothPairing

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction.GreenSource
open SaturationMonoid.PhysicsCore Stage10.StaticGreen Stage9C.Material.SpinPair
open MeasureTheory BasinRefinement SourceGaussianModel SourceFiniteData ContinuousGradient
open scoped ContDiff SchwartzMap
noncomputable section

theorem sourceCurrent_smooth : ContDiff ℝ ∞ sourceCurrent := by
  have same : sourceCurrent = fun point => -4*spinScale*sourceDensity point := funext sourceCurrent_value
  rw [same]
  exact contDiff_const.mul (sourceDensity_contDiff ∞)

def sourceResidual (point : Point) : ℝ := -(2*lapse)*spatialLap sourcePotential point+sourceCurrent point

theorem sourceResidual_continuous : Continuous sourceResidual :=
  (continuous_const.mul (spatialLap_smooth sourcePotential_smooth).continuous).add sourceCurrent_smooth.continuous

theorem sourceResidual_test (test : Point → ℝ) (smooth : ContDiff ℝ ∞ test) (support : HasCompactSupport test) :
    (∫ point, test point*sourceResidual point) = 0 := by
  have weak := original_D3_weak_gauss (support.toSchwartzMap smooth)
  simp only [sourceEuler_laplacian] at weak
  have lap : (testLaplacian (support.toSchwartzMap smooth) : Point → ℝ) = spatialLap test :=
    (spatialLap_test (support.toSchwartzMap smooth)).symm
  simp only [lap] at weak
  have rearrange : (fun point => sourcePotential point*(-(2*lapse)*spatialLap test point)) =
      fun point => -(2*lapse)*(sourcePotential point*spatialLap test point) := by funext point; ring
  rw [rearrange, integral_const_mul, compact_pairing_laplacian sourcePotential_smooth smooth support] at weak
  have integrableLap := compact_mul_integrable (spatialLap_smooth sourcePotential_smooth).continuous smooth.continuous support
  have integrableCurrent := compact_mul_integrable sourceCurrent_smooth.continuous smooth.continuous support
  have integrand : (fun point => test point*sourceResidual point) =
      fun point => -(2*lapse)*(spatialLap sourcePotential point*test point)+sourceCurrent point*test point := by
    funext point; unfold sourceResidual; ring
  rw [integrand, integral_add (integrableLap.const_mul _) integrableCurrent, integral_const_mul]
  exact weak

theorem original_D3_pointwise_gauss (point : Point) :
    -(2*lapse)*spatialLap sourcePotential point+sourceCurrent point = 0 := by
  have zeroAE : sourceResidual =ᵐ[volume] (fun _ => 0) :=
    ae_eq_zero_of_integral_contDiff_smul_eq_zero sourceResidual_continuous.locallyIntegrable
      (fun test smooth support => sourceResidual_test test smooth support)
  have zero := (sourceResidual_continuous.ae_eq_iff_eq volume continuous_const).mp zeroAE
  exact congrFun zero point

end
end LAlanine40K2025.UnifiedAction.GreenSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
