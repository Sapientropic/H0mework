import H0mework.Versions.AB.Physics.MotherSource.StaticGreen.DensityMoment
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.GreenRegularity

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedAction.GreenSource
open SaturationMonoid.PhysicsCore Stage10.StaticGreen Stage9C.Material.SpinPair
open MeasureTheory BasinRefinement SourceGaussianModel ContinuousGradient GlobalSource SourceFiniteData
noncomputable section

def potentialDecayConstant : ℝ :=
  ‖4*spinScale/(8*Real.pi*lapse)‖*
    (densityMomentBound zeroJet zeroJet*nearMass+
      (∫ point : Point, ‖point‖*‖sourceDensity point‖)+(∫ point : Point, ‖sourceDensity point‖))

theorem sourcePotential_decay (point : Point) :
    ‖point‖*‖sourcePotential point‖ ≤ potentialDecayConstant := by
  have weighted := convolution_weighted_bound
    (bilinear sourceTerms densityMatrix zeroJet zeroJet)
    (source_bilinear_integrable zeroJet zeroJet)
    (sourceBilinearBound zeroJet zeroJet) (source_bilinear_uniform_bound zeroJet zeroJet)
    (density_moment_integrable zeroJet zeroJet) (densityMomentBound zeroJet zeroJet)
    (density_moment_uniform zeroJet zeroJet) point
  have result := mul_le_mul_of_nonneg_left weighted (norm_nonneg (4*spinScale/(8*Real.pi*lapse)))
  rw [sourcePotential_convolution, norm_mul]
  unfold potentialDecayConstant
  change ‖point‖*(‖4*spinScale/(8*Real.pi*lapse)‖*‖densityConvolution zeroJet zeroJet point‖) ≤ _
  calc
    _ = ‖4*spinScale/(8*Real.pi*lapse)‖*(‖point‖*‖densityConvolution zeroJet zeroJet point‖) := by ring
    _ ≤ _ := result

theorem potentialDecayConstant_nonnegative : 0 ≤ potentialDecayConstant := by
  simpa only [norm_zero, zero_mul] using sourcePotential_decay 0

theorem sourcePotential_far_bound (radius : ℝ) (positive : 0 < radius) (point : Point)
    (outside : radius ≤ ‖point‖) : ‖sourcePotential point‖ ≤ potentialDecayConstant/radius := by
  apply (le_div_iff₀ positive).mpr
  calc
    _ ≤ ‖sourcePotential point‖*‖point‖ := mul_le_mul_of_nonneg_left outside (norm_nonneg _)
    _ = ‖point‖*‖sourcePotential point‖ := mul_comm _ _
    _ ≤ _ := sourcePotential_decay point

end
end LAlanine40K2025.UnifiedAction.GreenSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
