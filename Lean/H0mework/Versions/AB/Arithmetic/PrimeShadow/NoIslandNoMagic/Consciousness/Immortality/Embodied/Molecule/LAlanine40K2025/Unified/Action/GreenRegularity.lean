import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.ConvolutionSmooth
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.GreenPotential
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.StaticEnergy

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction.GreenSource
open SaturationMonoid.PhysicsCore Stage10.StaticGreen Stage9C.Material.SpinPair
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineCoframeLocalDifferentiability
open StageNineCanonicalCauchyState Stage10.CanonicalGauss
open MeasureTheory BasinRefinement SourceGaussianModel SourceFiniteData ContinuousGradient SourceCoulomb
open scoped ContDiff
noncomputable section

theorem densityConvolution_source (point : Point) :
    densityConvolution zeroJet zeroJet point =
      ∫ sourcePoint : Point, sourceDensity sourcePoint*kernel (point-sourcePoint) := by
  have translated := integral_sub_left_eq_self
    (fun sourcePoint : Point => sourceDensity sourcePoint*kernel (point-sourcePoint)) volume point
  simp only [sub_sub_cancel] at translated
  convert translated using 1
  rfl

theorem sourcePotential_convolution (point : Point) :
    sourcePotential point = (4*spinScale/(8*Real.pi*lapse))*densityConvolution zeroJet zeroJet point := by
  rw [sourcePotential_density, densityConvolution_source]
  simp_rw [green_kernel, ← mul_div_assoc]
  rw [integral_div]
  ring

theorem sourcePotential_smooth : ContDiff ℝ ∞ sourcePotential := by
  have same : sourcePotential = fun point =>
      (4*spinScale/(8*Real.pi*lapse))*densityConvolution zeroJet zeroJet point :=
    funext sourcePotential_convolution
  rw [same]
  exact contDiff_const.mul (convolution_smooth zeroJet zeroJet)

def fieldPotential (point : BasePoint) : ℝ := sourcePotential (spatialPoint 1 point)

theorem fieldPotential_smooth : ContDiff ℝ ∞ fieldPotential :=
  sourcePotential_smooth.comp (sourceSpatialMap 1).contDiff

theorem fieldPotential_regular : ScalarRegular fieldPotential := by
  refine ⟨fieldPotential_smooth.differentiable (by simp), ?_⟩
  intro index
  have derivative := (contDiff_infty_iff_fderiv.mp fieldPotential_smooth).2
  exact (derivative.clm_apply contDiff_const).differentiable (by simp)

theorem original_D3_generated_hamiltonian (space : StageNineSpatialPoint) :
    StaticEnergy.D3Difference (abelianPotential fieldPotential) 1 space =
      -lapse*Stage10.TemporalGauge.squared
        (Stage10.TemporalGauge.electric (abelianPotential fieldPotential) (canonicalCauchySlicePoint 0 space)) +
      4*spinScale*fieldPotential (canonicalCauchySlicePoint 0 space)*
        sourceDensity (spatialPoint 1 (canonicalCauchySlicePoint 0 space)) :=
  StaticEnergy.original_D3_hamiltonian fieldPotential fieldPotential_regular.1 1 space

end
end LAlanine40K2025.UnifiedAction.GreenSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
